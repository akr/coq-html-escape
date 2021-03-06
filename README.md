# coq-html-escape

Supplement material for the presentation at RubyKaigi 2017:
Ruby Extension Library Verified using Coq Proof-assistant,
Tanaka Akira,
2017-09-20,
http://rubykaigi.org/2017/presentations/tanaka_akr.html

This project contains a Ruby extention library for
HTML escape function using SSE verified by Coq.

## Home Page

https://github.com/akr/coq-html-escape

## Requirements

- Coq 8.9 (Coq 8.8 doesn't work)
- codegen plugin https://github.com/akr/codegen
- monadification plugin https://github.com/akr/monadification

## How to Build

  cd coq
  make
  cd ../ruby
  ruby extconf.rb
  make

## Directory Structure

- slide/2017-09-20-akr-rubykaigi.pdf : slide for RubyKaigi 2017
- coq/theories/natutils.v : utilities for nat
- coq/theories/listutils. : utilities for list (seq)
- coq/theories/assoc.v : assoc function
- coq/theories/ssrstr.v : SSReflect style for ascii and string
- coq/theories/imp.v : HTML escape/unescape function (including escape using SSE)
- coq/theories/spec.v : inductive specification for escape/unescape
- coq/theories/correct.v : correctness proof
- coq/theories/success.v : success proff using monadification plugin
- coq/theories/gen.v : code generation script using codegen plugin
- coq/gen/esc.c generated C source code
- ruby/verified_html_escape.c : glue code for Ruby
- ruby/benchmark/bench.rb : benchmark script
- ruby/benchmark/size-time.png : plot between size to time
- ruby/benchmark/ratio-slope-point.png : plot between escratio to size/time
- ruby/benchmark/ratio-slope-smooth.png : plot between escratio to size/time

## Link

- https://github.com/akr/coq-html-escape This project
- https://github.com/akr/monadification monadification plugin
- https://github.com/akr/codegen codegen plugin

## Author

Tanaka Akira
