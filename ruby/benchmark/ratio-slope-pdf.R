library(ggplot2)
d <- read.csv("benchmark/result.csv")
d$k <- d$time.s. / d$size.byte.
pdf("benchmark/ratio-slope.pdf", width=8, height=5)
ggplot(d, aes(esc_ratio, k, color=method)) +
  geom_point(size=0.1) +
  scale_x_continuous("escape character ratio") +
  scale_y_continuous("time / size [s/byte]", limits = c(0, 3e-8)) +
  theme(
    legend.justification=c(1,0),
    legend.position=c(1,0),
    text = element_text(size=25))
