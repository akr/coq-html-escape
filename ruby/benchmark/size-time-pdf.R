library(ggplot2)
d <- read.csv("benchmark/result.csv")
d$k <- d$time.s. / d$size.byte.
pdf("benchmark/size-time.pdf", width=8, height=5)
ggplot(d, aes(size.byte., time.s., color=esc_ratio, shape=method)) +
  geom_point(size=0.1) +
  scale_x_continuous("size[byte]") +
  scale_y_continuous("time[s]")
