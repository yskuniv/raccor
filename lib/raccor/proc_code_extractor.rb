module ProcCodeExtractor
  require 'ripper'

  class ParseHelper
    module Enumerable
      class EnumerableBuffer
        def initialize(enum)
          @enum_wrapper = Enumerator.new { |y|
            enum.each do |item| y << item; end
          }
          @buffer = []
        end

        def fetch(nth)
          prepare_to_fetch(nth)

          @buffer[nth]
        end

        def at(nth)
          begin
            fetch(nth)
          rescue IndexError
            nil
          end
        end

        def sub(nth)
          prepare_to_fetch(nth)

          Enumerator.new { |y|
            nth.step do |i|
              y << begin
                     fetch(i)
                   rescue IndexError
                     break
                   end
            end
          }.lazy
        end

        alias :[] :at


        private

        def prepare_to_fetch(nth)
          n = [(nth + 1) - @buffer.count, 0].max
          n.times do
            @buffer << begin
                         @enum_wrapper.next
                       rescue StopIteration
                         raise IndexError.new
                       end
          end
        end
      end


      def fold_map(init = nil, &block)
        initializer, iterator = case
                                when init
                                  [
                                    proc { |_| init },
                                    self
                                  ]
                                else
                                  [
                                    proc { |y| e = first; y << e; e },
                                    drop(1)
                                  ]
                                end

        Enumerator.new { |y|
          s = initializer[y]
          iterator.each do |item|
            s = block[s, item]
            y << s
          end
        }
      end

      def cons_iterator(&block)
        eb = EnumerableBuffer.new(self)

        Enumerator.new { |y|
          0.step do |nth|
            y << begin
                   eb.sub(nth)
                 rescue IndexError
                   break
                 end
          end
        }.lazy
      end
    end


    class Token
      def initialize(token)
        pos, event, ident = token

        @pos = pos
        @event = event
        @ident = ident
      end

      attr_reader :pos, :event, :ident
    end

    class TokenMatcher
      class Element
        def initialize(event: nil, ident: nil)
          @event = event
          @ident = ident
        end

        def match?(token)
          token &&
            (@event ? @event == token.event : true) &&
            (@ident ? @ident == token.ident : true)
        end
      end

      class TreeRoot
        def initialize(children = [])
          @children = children
        end

        def match?(tokens)
          @children.empty? ? true : @children.any? { |node| node.match?(tokens) }
        end

        attr_accessor :children
      end

      class TreeNode
        def initialize(element, children = [])
          @element = element
          @children = children
        end

        def match?(tokens)
          head, tail = tokens.first, tokens.drop(1)

          @element.match?(head) &&
            (@children.empty? ? true : @children.any? { |node| node.match?(tail) })
        end

        attr_accessor :element, :children
      end

      class << self
        alias :[] :new
      end


      def initialize(*sequence)
        children = parse_sequence(sequence)
        @tree_root = TreeRoot.new(children)
      end

      def match?(tokens, strict_match: false)
        tokens_ = case strict_match
                  when false
                    return false if ignored_token?(tokens.first)
                    tokens.reject { |token| ignored_token?(token) }
                  else
                    tokens
                  end

        @tree_root.match?(tokens_)
      end

      alias :=~ :match?


      private

      def parse_sequence(sequence)
        dummy_root = TreeRoot.new

        current_parents = [dummy_root]
        loop do
          x = sequence.shift or break

          parent = (current_parents.count == 1) ? current_parents.first : raise(NotImplementedError.new)

          parent.children = case x
                            when Array
                              parse_patterns(x)
                            else
                              [parse_item(x)]
                            end

          current_parents = parent.children
        end

        dummy_root.children
      end

      def parse_patterns(patterns)
        patterns.flat_map { |ptn|
          case ptn
          when Array
            parse_sequence(ptn)
          else
            [parse_item(ptn)]
          end
        }
      end

      def parse_item(x)
        arg = case x
              when String
                { ident: x }
              when Hash
                x
              else
                raise TypeError.new
              end

        TreeNode.new(Element.new(arg))
      end

      def ignored_token?(token)
        [
          :on_sp,
          :on_ignored_nl,
          :on_comment
        ].any? { |ev| token.event == ev }
      end
    end

    class SexpMatcher
      class << self
        alias :[] :new
      end


      def initialize(*pattern_list)
        @pattern_list = pattern_list
      end

      def match?(sexp)
        return false unless sexp

        @pattern_list.any? { |pattern| submatch(pattern, sexp) }
      end

      alias :=~ :match?


      private

      def submatch(pattern, sexp)
        return false unless pattern.is_a?(Array) && sexp.is_a?(Array) &&
                            pattern.count <= sexp.count

        pattern.zip(sexp).all? { |itm_p, itm_s|
          case itm_p
          when Array
            submatch(itm_p, itm_s)
          else
            itm_p ? itm_p == itm_s : true
          end
        }
      end
    end


    class << self
      def token_iterator(path)
        src = open(path)

        tokenize(src).
          extend(ParseHelper::Enumerable).cons_iterator
      end


      private

      def tokenize(src)
        Ripper.lex(src).
          map { |raw| Token.new(raw) }
      end
    end
  end

  class ExtractionError < StandardError; end

  class MultipleProcsFoundError < ExtractionError
    def initialize
      super('multiple procs found on the target line')
    end
  end


  class << self
    BeginningOfProcPattern = ParseHelper::TokenMatcher[
      [
        ['Proc', '.', 'new', ['do',
                              '{']],
        ['proc', ['do',
                  '{']],
        ['lambda', ['do',
                    '{']],
        ['->', ['do',
                '{']]
      ]
    ]

    ProcCodePattern = ParseHelper::SexpMatcher[
      [:program, [[:method_add_block]]],
      [:program, [[:lambda]]],
    ]


    def extract(proc)
      proc_filepath, proc_linum = proc.source_location

      iter = ParseHelper.token_iterator(proc_filepath).
               # discard tokens existing before the target line
               drop_while { |tokens| token_linum, _ = tokens.first.pos; token_linum < proc_linum }.
               # trim unnecessary tokens before the target proc
               drop_while { |tokens| BeginningOfProcPattern !~ tokens }

      # find index of the target proc end
      proc_end_index = iter.
                         map(&:first).map(&:ident).extend(ParseHelper::Enumerable).fold_map(&:+).
                         find_index { |str| ProcCodePattern =~ Ripper.sexp(str) }
      num_proc_tokens = proc_end_index + 1

      # check if no other procs exist on the same line
      raise MultipleProcsFoundError.new if iter.drop(num_proc_tokens).
                                             take_while { |tokens| token_linum, _ = tokens.first.pos; token_linum == proc_linum }.
                                             find { |tokens| BeginningOfProcPattern =~ tokens }

      iter.take(num_proc_tokens).
        map(&:first).map(&:ident).inject(&:+)
    end
  end
end
