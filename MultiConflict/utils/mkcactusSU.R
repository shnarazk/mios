#!/usr/bin/env Rscript

library("ggplot2")
target = "cactus2015-SU.pdf"
sutype = read.csv("problems.csv", header=T, sep=",", comment="#")[,3]

getData <- function (f) {
	df1 = read.csv(f, header=T, sep=",", comment="#")
	df1 = transform(df1, type=sutype)
	# sat
	df2 = subset(df1, type==1)
	df2 = df2[order(df2[,4]),]         	# sort by time (the 4th column)
	df2[[2]] = 1:nrow(df2)            	# reassign rownumbers
	# unsat
	df3 = subset(df1, type==-1)
	df3 = df3[order(df3[,4]),]         	# sort by time (the 4th column)
	df3[[2]] = 1:nrow(df3)            	# reassign rownumbers
	list(df2, df3)
	}

graph <- function (d) {
      g <- ggplot(d[[1]], aes(num, time, color=solver))
      g <- g + geom_point(data=d[[1]])
      g <- g + geom_line(data=d[[1]], size=0.8)
      g <- g + geom_point(data=d[[2]], aes(50+num, time))
      g <- g + geom_line(data=d[[2]], aes(50+num, time), size=0.5)
      g <- g + theme(legend.position = c(0.32,0.2), legend.justification = c(1,0))
      g <- g + scale_x_continuous(limits=c(0,80),breaks=seq(0,80,10))
      g <- g + scale_y_continuous(limits=c(0,1101) ,breaks=seq(0,1100,200))
      g <- g + xlab("#solved SAT + #solved UNSAT") + ylab("execution time [sec]") + ggtitle("Cactus Plot on SAT-Race 2015 SAT/UNSAT")
      print(g)
}

merge <- function (v, x) { if (is.null(v)) { x } else { list(rbind(v[[1]], x[[1]]),  rbind(v[[2]], x[[2]])) } }

merged = NULL
runs <- read.csv("runs", comment="#", sep=",", header=F)
for(run in runs[,1]) { merged = merge(merged, getData(run)); }

pdf(target, width=10, height=7)
graph(merged)
ggsave(target)
#ggsave(file="cactus2015-SU.png", width=9, height=6, dpi=200)
dev.off()
