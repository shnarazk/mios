#!/usr/bin/env Rscript
# USAGE:
# R_LIBS_USER=~/Sources/R
# cat mkSATgraph.R | R --vanilla
library("ggplot2")

target="cactus2015.pdf"
getData <- function (f) {
	df1 = read.csv(f, header=T, sep=",", comment="#")
	df2 = df1[order(df1[,4]),]         	# sort by time (the 4th column)
	df2[[2]] = 1:nrow(df2)            	# reassign rownumbers
	df2
	}

graph <- function (d = merged) {
      g <- ggplot(merged, aes(num, time, color=solver))
      g <- g + geom_point()
      g <- g + geom_line(data=merged,size=0.6)
      g <- g + theme(legend.position = c(0.38,0.2), legend.justification = c(1,0))
      g <- g + scale_x_continuous(limits=c(0,130),breaks=seq(0,130,10))
     g <- g + scale_y_continuous(limits=c(0,1100) ,breaks=seq(0,1100,200))
      g <- g + xlab("#solved") + ylab("execution time [sec]") + ggtitle("Cactus Plot on SAT-Race 2015 main track subset")
      print(g)
}

#minisat1 = getData("Formal/minisat-1.14.csv")
#minisat2 = getData("Formal/minisat-2.2.csv")
#minisatScale = minisat2
#minisatScale$time = 2.0 * minisatScale$time
#minisatScale$solver="2.0 * minisat-2.2"
#glucose1 = getData("Formal/glucose-4.0.csv")
# TODO glucose2 = getData("Formal/sr15m131-glucose-paralell.csv")
#merged = minisat1
#merged = rbind(merged, minisatScale)
#merged = rbind(merged, minisat2)
#merged = rbind(merged, glucose1)
#merged = rbind(merged, getData("Formal/sr15m131-toysat-0.4-P-2400-2016-02-20.csv"))
#merged = minisat2
merged = NULL
runs <- read.csv("runs", comment="#", sep=",", header=F)
for(run in runs[,1]) { merged = rbind(merged, getData(run)); }

pdf(target, width=10, height=7)
graph(merged)
ggsave(target)
# ggsave(file="cactus2015.png", width=9, height=6, dpi=200)
dev.off()
