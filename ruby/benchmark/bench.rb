require 'cgi'
require 'verified_html_escape'

methods = %w[sse_html_escape trec_html_escape CGI.escapeHTML]

puts "size[byte],method,esc_ratio,time[s]"

max_size = 40000
num_sizes = 200

num_ratios = 50

code = []
methods.each {|meth|
  num_sizes.times {
    num_ratios.times {
      sz = 1+rand(max_size-1)
      esc_ratio = rand
      code << <<~End
        sz = #{sz}
        meth = #{meth.dump}
        esc_ratio = #{esc_ratio}
        num_escape = (sz * esc_ratio).to_i
        src = (['a'] * (sz - num_escape) + ['&'] * num_escape).shuffle.join
        GC.disable
        t1 = Process.clock_gettime(Process::CLOCK_THREAD_CPUTIME_ID)
        dst = #{meth}(src)
        t2 = Process.clock_gettime(Process::CLOCK_THREAD_CPUTIME_ID)
        GC.enable
        t = t2-t1
        puts "\#{sz},\#{meth},\#{esc_ratio},\#{t}"
      End
    }
  }
}
eval code.shuffle.join
