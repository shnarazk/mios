#!/usr/bin/env Rscript

library("MASS")
library("KernSmooth")

arg1 = commandArgs(trailingOnly=TRUE)[1]
d = read.csv(arg1, header=T, sep=",", comment="#")

bx <- max(0.1, bandwidth.nrd(d[,1]))
by <- max(0.1, bandwidth.nrd(d[,2]))
k <- kde2d(d[,1], d[,2], c(bx, by), n=30)

png(paste(arg1, "-dens.png", sep=""))
image(k)
dev.off()

png(paste(arg1, "-contour.png", sep=""))
contour(k)
dev.off()
