rm(list= ls())

library(dplyr)
library(magrittr)
library(tidyr)
library(stringr)
library(openxlsx)
library(data.table)
library(lubridate)
library(tidyverse)
library(eeptools)
library(fNonlinear)
library(CombMSC)
library(zoo)
library(tseriesChaos)
library(seas)
library(tseries)
library(NTS)
library(TSA)
library(tsDyn)
library(BAYSTAR)
library(sm)
library(forecast)
library(Matrix)
library(mnormt)
library(MASS)
library(lattice)
library(coda)
library(matrixcalc)
library(MCMCpack)
library(mvtnorm)
library(Brobdingnag)
library(cubature)
library(bayesSurv)
library(TSA)
library(tseriesChaos)
library(tsDyn)
library(FindAllRoots)
library(lmtest)
library(FitAR)
library(forecast)
library(astsa)

######################## TAR
######################## TAR

#############################         INICIO DE PROGRAMA




####################  Estimaci?n de los coeficientes autorregresivos y ex?genos      
########################    tar2.coeffx




tar2.coeffx=function(reg, ay, p, q, sig, lagd, thres, mu0, v0, lagp1, lagp2, lagq1, lagq2, constant, thresVar) 
{
  P <- max(max(lagp1), max(lagp2), max(lagq1), max(lagq2)) 
  n <- length(ay)
  lag.y <- thresVar[(P + 1 - lagd):(n - lagd)]
  yt <- ay[(P + 1):n]
  x.1 <- matrix(NA, nrow = p+q, ncol = (n - P))
  if (reg == 1) {
    for (i in 1:p) {
      x.1[i, ] <- ay[(P - lagp1[i] + 1):(n - lagp1[i])]
    }
    for (i in 1:q) {
      x.1[p+i, ] <- thresVar[(P - lagq1[i] + 1):(n - lagq1[i])]
    }
    if (constant == 1) {
      tx <- cbind(1, t(x.1[, lag.y <= thres]))
    }
    else {
      tx <- t(x.1[, lag.y <= thres])
    }
    yt <- matrix(yt[lag.y <= thres], ncol = 1)
    sigma <- (t(tx) %*% tx)/sig + v0
    mu <- solve(sigma,(t(tx) %*% yt)/sig + v0 %*% mu0)
    ph <- rmvnorm(n = 1, mu, solve(sigma), method = "chol")
  }
  else {
    for (i in 1:p) {
      x.1[i, ] <- ay[(P - lagp2[i] + 1):(n - lagp2[i])]
    }
    for (i in 1:q) {
      x.1[p+i, ] <- thresVar[(P - lagq2[i] + 1):(n - lagq2[i])]
    }
    if (constant == 1) {
      tx <- cbind(1, t(x.1[, lag.y > thres]))
    }
    else {
      tx <- t(x.1[, lag.y > thres])
    }
    yt <- matrix(yt[lag.y > thres], ncol = 1)
    sigma <- (t(tx) %*% tx)/sig + v0
    mu <- solve(sigma,(t(tx) %*% yt)/sig + v0 %*% mu0)
    ph <- rmvnorm(n = 1, mu, solve(sigma), method = "chol")
  }
  return(ph)
}

#################################################################
#################################################


######################     PARA LA NORMAL BIVARIADA (c?lculo de la autocovianza)

rho=0.5
m=rep(0,2)
c=matrix(c(1.33,rho*1.33,rho*1.33,1.33),2,2)
lower=c(-Inf,-Inf)
upper1=c(0,0)
f1=pmvnorm(lower,upper1,mean=m,sigma=c)
f1


######################################################

############### Extraer la varianza de la distribuci?n de los errores      
##################  tar2.sigmax

tar2.sigmax=function(reg, ay, thres, lagd, p, q, ph, v, lambda, lagp1, lagp2, lagq1, lagq2, constant, thresVar) 
{
  P <- max(max(lagp1), max(lagp2), max(lagq1), max(lagq2)) 
  n <- length(ay)
  lag.y <- thresVar[(P + 1 - lagd):(n - lagd)]
  yt <- ay[(P + 1):n]
  x.1 <- matrix(NA, nrow = p+q, ncol = (n - P))
  phi <- matrix(ph, nrow = p+q+constant, ncol = 1)
  if (reg == 1) {
    m <- sum(lag.y <= thres)
    y<- matrix(yt[lag.y <= thres], ncol = 1)
    for (i in 1:p) {
      x.1[i, ] <- ay[(P - lagp1[i] + 1):(n - lagp1[i])]
    }
    for (i in 1:q) {
      x.1[p+i, ] <- thresVar[(P - lagq1[i] + 1):(n - lagq1[i])]
    }
    if (constant == 1) {
      tx <- cbind(1, t(x.1[, lag.y <= thres]))
    }
    else {
      tx <- t(x.1[, lag.y <= thres])
    }
    s2 <- (t(y - tx %*% phi) %*% (y - tx %*% phi))/m
  }
  else {
    m <- sum(lag.y > thres)
    y <- matrix(yt[lag.y > thres], ncol = 1)
    for (i in 1:p) {
      x.1[i, ] <- ay[(P - lagp2[i] + 1):(n - lagp2[i])]
    }
    for (i in 1:q) {
      x.1[p+i, ] <- thresVar[(P - lagq2[i] + 1):(n - lagq2[i])]
    }
    if (constant == 1) {
      tx <- cbind(1, t(x.1[, lag.y > thres]))
    }
    else {
      tx <- t(x.1[, lag.y > thres])
    }
    s2 <- (t(y - tx %*% phi) %*% (y - tx %*% phi))/m
  }
  shape <- (v + m)/2
  rate <- (v * lambda + m * s2)/2
  sigma <- 1/rgamma(1, shape, rate)
  #sigma <- 1/rgamma(1, shape, rate)
  return(sigma)
}

#############################################################################
##########################################


###################### calcular la funci?n log.verosimil       
############################ tar2.likx

tar2.likx=function(ay, p1, p2, q1, q2, ph.1, ph.2, sig.1, sig.2, lagd, thres, lagp1, lagp2, lagq1, lagq2,  constant, thresVar) 
{
  
  P <- max(max(lagp1), max(lagp2), max(lagq1), max(lagq2)) 
  n <- length(ay)
  p.1 <- matrix(ph.1, nrow = p1 + q1 + constant, ncol = 1)
  p.2 <- matrix(ph.2, nrow = p2 + q2 + constant, ncol = 1)
  lag.y <- thresVar[(P + 1 - lagd):(n - lagd)]
  yt <- ay[(P + 1):n]
  n1 <- sum(lag.y <= thres)
  n2 <- sum(lag.y > thres)
  y.1 <- matrix(yt[lag.y <= thres], ncol = 1)
  y.2 <- matrix(yt[lag.y > thres], ncol = 1)
  x.1 <- matrix(NA, nrow = p1+q1, ncol = (n - P))
  for (i in 1:p1) {
    x.1[i, ] <- ay[(P - lagp1[i] + 1):(n - lagp1[i])]
  }
  for (i in 1:q1) {
    x.1[p1+i, ] <- thresVar[(P - lagq1[i] + 1):(n - lagq1[i])]
  }
  if (constant == 1) {
    tx.1 <- cbind(1, t(x.1[, lag.y <= thres]))
  }
  else {
    tx.1 <- t(x.1[, lag.y <= thres])
  }
  x.2 <- matrix(NA, nrow = p2+q2, ncol = (n - P))
  for (i in 1:p2) {
    x.2[i, ] <- ay[(P - lagp2[i] + 1):(n - lagp2[i])]
  }
  for (i in 1:q2) {
    x.2[p2+i, ] <- thresVar[(P - lagq2[i] + 1):(n - lagq2[i])]
  }
  if (constant == 1) {
    tx.2 <- cbind(1, t(x.2[, lag.y > thres]))
  }
  else  {
    tx.2 <- t(x.2[, lag.y > thres])
  }
  ln.li <- -(((n-P)*log(2*pi))/2) -((t(y.1 - tx.1 %*% p.1) %*% (y.1 - tx.1 %*% p.1))/(2 *sig.1)) - ((t(y.2 - tx.2 %*% p.2) %*% (y.2 - tx.2 %*% p.2))/(2 * sig.2)) - ((n1/2) * log(sig.1)) - ((n2/2) * log(sig.2))
  
  return(ln.li)
}


##################################################################################
##############################################################



###################### Extrae el valor umbral        
#############################   tar2.thresxG      Metropolis-Hasting, con densidad instrumental GAUSSIANA 


tar2.thresxG=function(ay, p1, p2, q1, q2, ph.1, ph.2, sig.1, sig.2, lagd, thres, step.r, h, bound, lagp1, lagp2, lagq1, lagq2,  constant,  thresVar) 
{
  P <- max(max(lagp1), max(lagp2), max(lagq1), max(lagq2)) 
  n <- length(ay)
  lag.y <- thresVar[(P + 1 - lagd):(n - lagd)]
  
  new.r <- thres + step.r*rnorm(1, mean = 0, sd = 1)
  m1<-sum(lag.y<=new.r)
  m2<-sum(lag.y>new.r)
  m<-c(m1,m2)
  
  
  repeat {
    if ((new.r < bound[1]) | (new.r > bound[2])| any(m<n/h) | any(m>=n)) 
    {
      
      new.r <- thres + step.r*rnorm(1, mean = 0, sd = 1)
      m1<-sum(lag.y<=new.r)
      m2<-sum(lag.y>new.r)
      m<-c(m1,m2)
    }
    else    break
  }
  
  old.lik <- tar2.likx(ay, p1, p2, q1, q2, ph.1, ph.2, sig.1, sig.2, lagd, thres, lagp1, lagp2, lagq1, lagq2, constant, thresVar)
  new.lik <- tar2.likx(ay, p1, p2, q1, q2, ph.1, ph.2, sig.1, sig.2, lagd, new.r, lagp1, lagp2, lagq1, lagq2, constant, thresVar)
  
  
  if ((new.lik - old.lik) > log(runif(1))) {
    r.count<-1
  }
  else {
    new.r <- thres
    r.count <- 0
  }
  
  umbral<-list(r.count=r.count, new.r=new.r)
  return(umbral)
}


######################################################################################
#############################################################




#############  Identificaci?n del rezago  d       
#####################    tar2.lagdx


tar2.lagdx=function (ay, p1, p2, q1, q2, ph.1, ph.2, sig.1, sig.2, thres, lagp1, lagp2, lagq1, lagq2, constant, d0, thresVar) 
{
  loglik <- lik <- NULL
  
  for (i in 1:(d0+1)) {
    
    loglik[i] <- tar2.likx(ay, p1, p2, q1, q2, ph.1, ph.2, sig.1, sig.2, (i-1), thres, lagp1, lagp2, lagq1, lagq2,  constant, thresVar)
    
  }
  lik <- exp(loglik - max(loglik))
  lagd <- (sum((cumsum(lik)/sum(lik)) < runif(1, min = 0, max = 1)))
  return(lagd)
}


###################################################################################
#####################################################



######################## c?lculo de estad?sticas resumen       
###############################################################  tar2.summaryx
#####  x es par.set del programa principal


tar2.summaryx=function (x, lagp1, lagp2, lagq1, lagq2,  constant) 
{
  n <- ncol(x)
  temp <- matrix(NA, n, 5)
  for (i in 1:n) 
  {
    
    temp[i, 1] <- mean(x[, i])
    temp[i, 2] <- median(x[, i])
    temp[i, 3] <- sd(x[, i])
    temp[i, 4:5] <- quantile(x[, i], c(0.025, 0.975))
    colnames(temp) <- c("media", "mediana", "d.e.", "inf.95", "sup.95")
    
    if(constant==1) {
      rownames(temp) <- c(paste("phi1", c(0, lagp1), sep = "."),paste("qhi1", lagq1, sep = "."), paste("phi2", c(0, lagp2), sep = "."),paste("qhi2", lagq2, sep = "."), "sigma^2 1", "sigma^2 2", "r")
    }
    if(constant==0) {
      rownames(temp) <- c(paste("phi1", lagp1, sep = "."),paste("qhi1", lagq1, sep = "."), paste("phi2", lagp2, sep = "."),paste("qhi2", lagq2, sep = "."), "sigma^2 1", "sigma^2 2", "r")
    }
    
  }
  return(temp)
}


###################################################################
####################################



########################################        programa principal    Estimaci?n Bayesiana, residuales   
##############################################       BAYES2.TARX


BAYES2.TARX=function(x, lagp1, lagp2, lagq1, lagq2, Iteration, Burnin, constant, step.thv, h,  thresVar, d0)
  
{
  refresh<-1000
  
  p1 <- length(lagp1)
  p2 <- length(lagp2)
  q1 <- length(lagq1)
  q2 <- length(lagq2)
  nx <- length(x)
  
  
  ########## condiciones iniciales #################
  
  phi.1=rep(0.05,p1+q1+constant)
  phi.2=rep(0.05,p2+q2+constant)
  sigma.1=0.20
  sigma.2=0.20
  
  lagd=3
  
  thres=median(thresVar)
  
  accept.r=0
  sum.r=0
  
  ############# hiperpar?metros ##############
  
  mu01=matrix(0,nrow=p1+q1+constant,ncol=1)
  v01=diag(0.1,p1+q1+constant)
  mu02=matrix(0,nrow=p2+q2+constant,ncol=1)
  v02=diag(0.1,p2+q2+constant)
  
  v0=3
  lambda0=var(x)/3
  bound.thv=c(min(thresVar),max(thresVar))
  
  
  
  ####################################################################
  
  par.set <- matrix(NA, nrow = Iteration, ncol = (length(c(phi.1, phi.2, sigma.1, sigma.2, thres, lagd))))
  loglik.1 <- loglik.2 <- DIC <-lnaprioris<-logvermarg<-NA
  
  for (igb in 1:Iteration) {
    
    phi.1 <- tar2.coeffx(1, x, p1, q1, sigma.1, lagd, thres, mu01, v01, lagp1, lagp2, lagq1, lagq2, constant, thresVar)
    phi.2 <- tar2.coeffx(2, x, p2, q2, sigma.2, lagd, thres, mu02, v02, lagp1, lagp2, lagq1, lagq2, constant, thresVar)
    sigma.1 <- tar2.sigmax(1, x, thres, lagd, p1, q1, phi.1, v0, lambda0, lagp1, lagp2, lagq1,lagq2,constant, thresVar)
    sigma.2 <- tar2.sigmax(2, x, thres, lagd, p2, q2, phi.2, v0, lambda0, lagp1, lagp2, lagq1,lagq2,constant, thresVar)
    lagd <- tar2.lagdx(x, p1, p2, q1,q2, phi.1, phi.2, sigma.1,sigma.2, thres, lagp1, lagp2, lagq1, lagq2, constant, d0, thresVar)
    thresholdt <- tar2.thresxG(x, p1, p2, q1, q2, phi.1, phi.2, sigma.1, sigma.2, lagd, thres, step.r = step.thv, h, bound.thv, lagp1, lagp2, lagq1, lagq2, constant, thresVar )
    
    sum.r <- sum.r + thresholdt$r.count
    thres <- thresholdt$new.r
    
    par.set[igb, ] <- c(phi.1, phi.2, sigma.1, sigma.2, thres, lagd)
    
    loglik.1[igb] <- tar2.likx(x, p1, p2, q1, q2, phi.1, phi.2, sigma.1, sigma.2, lagd, thres, lagp1, lagp2, lagq1, lagq2, constant, thresVar)
    
    lnaprioris[igb]<- -0.5*((p1+q1+constant)*log(2*pi)+(p1+q1+constant)*log(det(solve(v01)))+phi.1%*%v01%*%t(phi.1))-0.5*((p2+q2+constant)*log(2*pi)+(p2+q2+constant)*log(det(solve(v02)))+phi.2%*%v02%*%t(phi.2))+(1.5*log(var(x)/2)-log(gamma(1.5))-2.5*log(sigma.1)-0.5*var(x)*(1/sigma.1))+(1.5*log(var(x)/2)-log(gamma(1.5))-2.5*log(sigma.2)-0.5*var(x)*(1/sigma.2))+log(1/(bound.thv[2]-bound.thv[1]))+log(1/(d0+1))
    
    logvermarg[igb]<-loglik.1[igb]+lnaprioris[igb]
    
    
    ncol0 <- ncol(par.set)
    
    if (igb%%refresh == 0) 
    {
      cat("iteration = ", igb, "\n")
      cat("regime 1 = ", round(phi.1, 4), "\n")
      cat("regime 2 = ", round(phi.2, 4), "\n")
      cat("sigma^2 1  = ", round(sigma.1, 4), "\n")
      cat("sigma^2 2  = ", round(sigma.2, 4), "\n")
      cat("r        = ", round(thres, 4), "\n")
      accept.r <- (sum.r/igb) * 100
      cat("Tasa de aceptaci?n de r = ", round(accept.r, 4), "%", "\n")
      
      lag.freq <- rep(0, (d0+1))
      for (i in 1:(d0+1)) {
        lag.freq[i] <- sum(par.set[1:igb, ncol0] == (i-1))
      }
      lag.freq<-t(matrix(lag.freq, dimnames = list(c(as.character(0:d0)), c("Frec."))))
      cat("Escogencia del Rezago : ", "\n")
      print(lag.freq)
      cat("------------", "\n")
    }
    
  }   ### fin del igb
  
  
  
  mcmc.stat <- tar2.summaryx(par.set[(Burnin + 1):Iteration, 1:(ncol0 - 1)], lagp1, lagp2, lagq1, lagq2, constant)
  print(round(mcmc.stat, 4))
  
  lag.y <- c(0:d0)
  lag.d <- lag.y[lag.freq == max(lag.freq)]
  cat("Escogencia del Rezago : ", "\n")
  print(lag.freq)
  cat("------------", "\n")
  cat("La probabilidad a posterior m?s alta corresponde al rezago: ", lag.d, "\n")
  
  loglik.2<-tar2.likx(x, p1, p2, q1, q2, mcmc.stat[1:(p1 + q1 + constant), 1], mcmc.stat[(p1 + q1 + constant + 1):(p1 + q1 + constant + p2 + q2 + constant), 1], mcmc.stat[(p1 + q1 + constant + p2 + q2+ constant + 1), 1], mcmc.stat[(p1 + q1 + constant + p2 + q2 + constant + 2), 1], lag.d, mcmc.stat[(p1 + q1+ constant + p2 + q2 + constant + 3), 1], lagp1, lagp2, lagq1, lagq2, constant, thresVar)
  
  DIC<- (2*(-2*sum(loglik.1[(Burnin + 1):Iteration]))/length(loglik.1[(Burnin + 1):Iteration])) - (-2*loglik.2)
  cat(" DIC = ", DIC, "\n")
  
  #lnapriorisfijo<-NA
  #lnapriorisfijo<- -0.5*((p1+q1+constant)*log(2*pi)+(p1+q1+constant)*log(det(solve(v01)))+ t(mcmc.stat[1:(p1 + q1 + constant), 1])%*%v01%*%( mcmc.stat[1:(p1 + q1 + constant), 1]))-0.5*((p2+q2+constant)*log(2*pi)+(p2+q2+constant)*log(det(solve(v02)))+ t(mcmc.stat[(p1 + q1 + constant + 1):(p1 + q1 + constant + p2 + q2 + constant), 1])%*%v02%*%( mcmc.stat[(p1 + q1 + constant + 1):(p1 + q1 + constant + p2 + q2 + constant), 1]))+(1.5*log(var(x)/2)-log(gamma(1.5))-2.5*log(mcmc.stat[(p1 + q1 + constant + p2 + q2+ constant + 1), 1])-0.5*var(x)*(1/mcmc.stat[(p1 + q1 + constant + p2 + q2+ constant + 1), 1]))+(1.5*log(var(x)/2)-log(gamma(1.5))-2.5*log(mcmc.stat[(p1 + q1 + constant + p2 + q2+ constant + 2), 1])-0.5*var(x)*(1/mcmc.stat[(p1 + q1 + constant + p2 + q2+ constant + 2), 1]))+log(1/(bound.thv[2]-bound.thv[1]))+log(1/(d0+1))
  
  
  
  if (constant == 1) 
  {       con.1 <- mcmc.stat[1, 1]
  par.1 <- mcmc.stat[2:(p1+q1+constant), 1]
  con.2 <- mcmc.stat[p1+q1+constant+1, 1]
  par.2 <- mcmc.stat[(p1+q1+constant+1+1):(p1+q1+constant+p2+q2+constant), 1]
  sig.1u <- mcmc.stat[p1+q1+constant+p2+q2+constant+1,1]
  sig.2d <- mcmc.stat[p1+q1+constant+p2+q2+constant+2,1]
  thv   <- mcmc.stat[p1+q1+constant+p2+q2+constant+3, 1]
  }
  
  if (constant == 0) 
  {       con.1 <- 0
  par.1 <- mcmc.stat[1:(p1 + q1), 1]
  con.2 <- 0
  par.2 <- mcmc.stat[(p1 + q1+ 1):(p1 + q1 + p2 + q2), 1]
  sig.1u <- mcmc.stat[p1+q1+p2+q2+1,1]
  sig.2d <- mcmc.stat[p1+q1+p2+q2+2,1]
  thv   <- mcmc.stat[p1 + q1 + p2 +q2 + 3, 1]
  }
  
  maxd <- max(max(lagp1), max(lagp2),max(lagq1),max(lagq2))
  
  residual <-residual.est<- rep(0, (nx - maxd))
  residual1 <- residual2<- rep(0, (nx - maxd))
  
  
  
  for (t in (maxd + 1):nx) {
    
    if (thresVar[t - lag.d]<=thv) {
      residual[t - maxd] <- x[t] - sum(con.1, par.1[1:p1]*x[t - lagp1], par.1[(p1+1):(p1+q1)]*thresVar[t - lagq1])
      residual.est[t - maxd]<-residual[t - maxd]/sqrt(sig.1u)
      residual1[t - maxd] <- x[t] - sum(con.1, par.1[1:p1]*x[t - lagp1], par.1[(p1+1):(p1+q1)]*thresVar[t - lagq1])
    }
    else {
      residual[t - maxd] <- x[t] - sum(con.2, par.2[1:p2]*x[t - lagp2] , par.2[(p2+1):(p2+q2)]*thresVar[t - lagq2])
      residual.est[t - maxd]<-residual[t - maxd]/sqrt(sig.2d)
      residual2[t - maxd] <- x[t] - sum(con.2, par.2[1:p2]*x[t - lagp2], par.2[(p2+1):(p2+q2)]*thresVar[t - lagq2])
    }
    
  }
  res1<-sum(residual1^2)
  res2<-sum(residual2^2)
  lag.yy<-thresVar[(maxd+1-lag.d):(nx-lag.d)]
  n1<-sum(lag.yy<=thv)
  n2<-sum(lag.yy>thv)
  NAIC<-NA
  NAIC<-((n1*log(res1/n1)+2*(p1+q1+constant)) + (n2*log(res2/n2)+2*(p2+q2+constant)))/(n1+n2)
  cat("NAIC = ", NAIC, "\n")
  
  
  tar <- list(mcmc = par.set, posterior = par.set[(Burnin + 1):Iteration, 1:ncol0], coef = round(mcmc.stat, 4), residual = residual, residual.est=residual.est, lagd = lag.d, DIC = DIC, NAIC=NAIC, logverosimil=loglik.1[(Burnin+1):Iteration], log.ver=logvermarg[(Burnin+1):Iteration])
  
  return(tar)
  
}



####################################### UNA CORRIDA TARX-2reg.
setwd("D:/sarbelaez/Documents/Maestría/Tesis/Datos finales")
Datos=read.xlsx("Desempleo.xlsx")
ISE=ts(Datos$ISE_estacional[1:168],start = c(2005,1),freq=12)

Xt=diff(log(ISE))*100
Xt

TIB=read.xlsx("TIB.xlsx",startRow = 7,detectDates = T)
class(TIB$`Fecha(dd/mm/aaaa)`)
TIB$Fecha=as.Date(TIB$`Fecha(dd/mm/aaaa)`)

TIB$Año=as.numeric(format(TIB$Fecha,'%Y'))
TIB$Mes=as.numeric(format(TIB$Fecha,'%m'))

TIB_mensual=TIB%>%group_by(Año,Mes)%>%summarise(TIB=mean(`TIB.(Efectiva.anual).%`,na.rm=T))
TIB_mensual=TIB_mensual[119:286,]

TES=read.xlsx("TES_mensual.xlsx",startRow = 7,detectDates = T)
TES$`Año(aaaa)-Mes(mm)`=as.Date(TES$`Año(aaaa)-Mes(mm)`)
TES=TES[37:204,]
class(TES$`Año(aaaa)-Mes(mm)`)

TES$Año=as.numeric(format(TES$`Año(aaaa)-Mes(mm)`,'%Y'))
TES$Mes=as.numeric(format(TES$`Año(aaaa)-Mes(mm)`,'%m'))
TES_mensual=TES%>%group_by(Año,Mes)%>%summarise(TES=mean(`Tasa.a.10.años.%`))


Datos=as.data.frame(cbind(TES_mensual$TES,TIB_mensual$TIB))
names(Datos)=c("TES","TIB")
Datos$spread=Datos$TES-Datos$TIB

Spread=ts(Datos$spread,start = c(2005,1),freq=12)
Zt=diff(Spread)

x=Xt
thresVar=Zt

set.seed(525)

lagp1=c(1,2,12,13,14,24,25,26)
lagp2=c(12)
lagq1=1
lagq2=1
Iteration=12000
Burnin=4000
constant=0
step.thv=0.0525
h=25
d0=3


out2<-BAYES2.TARX(x, lagp1, lagp2, lagq1, lagq2, Iteration, Burnin, constant, step.thv, h,  thresVar, d0)
res=out2$residual.est
par(mfrow=c(2,1))
ts.plot(res,ylab="Resiudales estandarizados", xlab="Tiempo")   # VALIDAR SUPUESTOS CON RESIDUALES, de aquí en adelante...
hist(res,main="Histograma de residuales estandarizados")
boxplot(res)

par(mfrow=c(2,2))
acf(res, main="I",xlab="Tiempo",lag.max=50)        # función de autocorrelación muestral
pacf(res, main="II",xlab="Tiempo",ylab="PACF",lag.max=50)       # función de autocorrelación parcial muestral
jarque.bera.test(res) # prueba de normalidad

# Prueba CUSUM y CUSUM-SQ para los residuales del modelo (evidencia de una especifi
#cación correcta o no del modelo y heterocedasticidad, resp.)
cum=cumsum(res)/sd(res)
N=length(res)
cumq=cumsum(res^2)/sum(res^2)
Af=0.948 ###Cuantil del 95% para la estad?stica cusum
co=0.14213####Valor del cuantil aproximado para cusumsq para n/2
LS=Af*sqrt(N)+2*Af*c(1:length(res))/sqrt(N)
LI=-LS
LQS=co+(1:length(res))/N
LQI=-co+(1:length(res))/N
plot(cum,type="l",ylim=c(min(LI),max(LS)),xlab="Tiempo",ylab="CUSUM",main="III")
lines(LS,type="S",col="black")
lines(LI,type="S",col="black")
#CUSUMSQ
plot(cumq,type="l",xlab="Tiempo",ylab="CUSUMSQ",main="IV")                      
lines(LQS,type="S",col="black")                                                                           
lines(LQI,type="S",col="black")



par(mfrow=c(1,1))
car::qqPlot(res)
qqline(res)

B=matrix(NA,nrow=36,ncol=1)
for (i in 1:36) {
  A=Box.test(res, lag = i, type = "Ljung-Box")
  B[i,1]=A$p.value
}


#Estimación modelo AR variable de umbral
forecast::Acf(Zt, main="",xlab="Tiempo",ylab="ISE original",lag.max=50)        # función de autocorrelación muestral
forecast::Pacf(Zt, main="",xlab="Tiempo",ylab="ISE original",lag.max=50)       # función de autocorrelación parcial muestral
Modelo.zt=forecast::Arima(Zt,order=c(1,0,0),include.constant = F,fixed=c(NA))
lmtest::coeftest(Modelo.zt)

#######################################   PRONOSTICOS



tar.summarymedia=function(x) 
{
  h <- ncol(x)
  tempm <- matrix(NA, h, 1)
  for (i in 1:h) 
  {
    tempm[i, 1] <- mean(x[, i])
  }
  return(tempm)
}


####################### c?lculo de estad?sticas resumen       tar.summarypron


tar.summarypron=function(x,n) 
{
  h <- ncol(x)
  temp <- matrix(NA, h, 6)
  for (i in 1:h) 
  {
    
    temp[i, 1] <- mean(x[, i])
    temp[i, 2] <- sd(x[, i])
    temp[i, 3:4] <- quantile(x[, i], c(0.05, 0.95))
    temp[i, 5:6] <- quantile(x[, i], c(0.025, 0.975))
    colnames(temp) <- c("media", "d.e.", "inf.90", "sup.90", "inf.95", "sup.95")
    rownames(temp)<- c(paste("",(n+1):(n+h),sep="")) 
  }
  return(temp)
}






####################################################################################





######  PRONOSTICOS PARA DATOS REALES


pronosticos<-function(LH, x, thresVar, Iteration, Burnin, step.thv, d0)
{
  
  
  L=2           # n?mero de reg?menes
  nx=length(x)
  
  lagp1=c(1,2,12,13,14,24,25,26)
  lagq1=1
  lagp2=c(12)
  lagq2=1
  
  
  lagpr<-vector("list",L)
  lagqr<-vector("list",L)
  
  lagpr[[1]]<-lagp1
  lagqr[[1]]<-lagq1
  lagpr[[2]]<-lagp2
  lagqr[[2]]<-lagq2
  
  
  p1 <- length(lagp1)
  q1 <- length(lagq1)
  p2 <- length(lagp2)
  q2 <- length(lagq2)
  
  NN<-Iteration-Burnin
  constant<-0
  h<-25
  
  oarp=c(p1,p2)       ## ordenes autorregresivos para los dos reg?menes
  oarq=c(q1,q2)       ## ordenes autorregresivos exogenos para los dos reg?menes
  
  
  
  out2<-BAYES2.TARX(x, lagp1, lagp2, lagq1, lagq2, Iteration, Burnin, constant, step.thv, h,  thresVar, d0)
  salida2=out2$posterior
  
  
  conpron=vector("list",L)
  parpron=vector("list",L)
  sigpron=vector("list",L)
  
  if (constant==1)
  {
    conpron[[1]]=salida2[,1]
    parpron[[1]]=salida2[,2:(p1+q1+1)]
    conpron[[2]]=salida2[,p1+q1+2]
    parpron[[2]]=salida2[,(p1+q1+3):(p1+q1+p2+q2+2)]
    sigpron[[1]]=salida2[,p1+q1+p2+q2+3]
    sigpron[[2]]=salida2[,p1+q1+p2+q2+4]
    thres=salida2[,p1+q1+p2+q2+5]
    lagd=salida2[,p1+q1+p2+q2+6]
  }
  
  if (constant==0)
  {
    conpron[[1]]=matrix(0,nrow=(Iteration-Burnin),ncol=1)
    parpron[[1]]=salida2[,1:(p1+q1)]
    conpron[[2]]=matrix(0,nrow=(Iteration-Burnin),ncol=1)
    parpron[[2]]=salida2[,(p1+q1+1):(p1+q1+p2+q2)]
    sigpron[[1]]=salida2[,p1+q1+p2+q2+1]
    sigpron[[2]]=salida2[,p1+q1+p2+q2+2]
    thres=salida2[,p1+q1+p2+q2+3]
    lagd=salida2[,p1+q1+p2+q2+4]
    
  }
  
  seriex=matrix(0,nrow=NN, ncol=LH)
  seriez=matrix(0,nrow=NN, ncol=LH)
  
  for (i in 1:NN)
  {
    
    xv=ts(rep(0,nx+LH))
    xv[1:nx]=x
    zv=ts(rep(0,nx+LH))
    zv[1:nx]=thresVar
    
    for (hh in 1:LH)
    {
      zv[nx+hh]=0.18934*zv[nx-hh-1]+rnorm(1, mean=0, sd=sqrt(0.2973))  ## el kernel de transici?n, variable umbral
      
    }
    
    
    
    for (h in 1:LH)
    {
      
      if (zv[nx-lagd[i]+h]<=thres[i]){
        
        SJ<-1
      }
      if (zv[nx-lagd[i]+h]>thres[i]){
        
        SJ<-2
      }
      
      X1=0
      for (k in 1:oarp[SJ])
      {
        X1=X1+parpron[[SJ]][i,k]*xv[nx+h-lagpr[[SJ]][k]]
      }
      
      XX1=0
      for (kk in 1:oarq[SJ])
      {
        XX1=XX1+parpron[[SJ]][i,oarp[SJ]+kk]*zv[nx+h-lagqr[[SJ]][kk]]
      }
      
      xv[nx+h]=sum(conpron[[SJ]][i],X1,XX1,rnorm(1, mean=0,sd=sqrt(sigpron[[SJ]][i])))
      
      seriex[i,h]=xv[nx+h]
      seriez[i,h]=zv[nx+h]
      
    }
  }
  
  pron<-list(seriex=seriex, seriez=seriez)
  return(pron)
}

########################################################################

#########################
###########Pronósticos un paso adelante

LH=1
Iteration=20000
Burnin=8000
step.thv<-0.0525
d0=3
AA<-matrix(NA,nrow=15, ncol=LH)


for (i in 0:14) {
  set.seed(525)
  Datos=read.xlsx("Desempleo.xlsx")
  Datos=Datos[1:(168+i),]
  ISE=ts(Datos$ISE_estacional,start = c(2005,1),freq=12)
  Xt=diff(log(ISE))*100
  Xt=ts(Xt,start=c(2005,2),freq=12)
  TIB=read.xlsx("TIB.xlsx",startRow = 7,detectDates = T)
  TIB$Fecha=as.Date(TIB$`Fecha(dd/mm/aaaa)`)
  TIB$Año=as.numeric(format(TIB$Fecha,'%Y'))
  TIB$Mes=as.numeric(format(TIB$Fecha,'%m'))
  
  TIB_mensual=TIB%>%group_by(Año,Mes)%>%summarise(TIB=mean(`TIB.(Efectiva.anual).%`,na.rm=T))
  TIB_mensual=TIB_mensual[119:(286+i),]
  
  TES=read.xlsx("TES_mensual.xlsx",startRow = 7,detectDates = T)
  TES$`Año(aaaa)-Mes(mm)`=as.Date(TES$`Año(aaaa)-Mes(mm)`)
  TES=TES[(37-i):204,]
  class(TES$`Año(aaaa)-Mes(mm)`)
  
  TES$Año=as.numeric(format(TES$`Año(aaaa)-Mes(mm)`,'%Y'))
  TES$Mes=as.numeric(format(TES$`Año(aaaa)-Mes(mm)`,'%m'))
  TES_mensual=TES%>%group_by(Año,Mes)%>%summarise(TES=mean(`Tasa.a.10.años.%`))
  
  Datos=as.data.frame(cbind(TES_mensual$TES,TIB_mensual$TIB))
  names(Datos)=c("TES","TIB")
  Datos$spread=Datos$TES-Datos$TIB
  
  Spread=ts(Datos$spread,start = c(2005,1),freq=12)
  
  
  Zt=diff(Spread,lag=1)
  x2=Xt
  thresVar2=Zt
  
  p=pronosticos(LH, x2, thresVar2, Iteration, Burnin, step.thv, d0)
  px=p$seriex
  pz=p$seriez
  AA[i+1,]= t(tar.summarymedia(px))
}


Pronostico=ts(AA[,1],start=c(2019,1),freq=12)
Comparacion=read.xlsx("Desempleo.xlsx")
Comparacion=Comparacion[168:183,]
Comp_des=ts(Comparacion$ISE_estacional,start = c(2018,12),freq=12)
Comp_des=diff(log(Comp_des))*100
par(mfrow=c(1,1))


data=as.data.frame(as.yearmon(time(Comp_des)))
names(data)="Mes"
data$Obsevado=Comp_des
data$Predicho=Pronostico

data$Mes
plot(data$Mes,
     data$Obsevado,
     type = "l",
     col = 1,
     xlab = "Year",
     ylab = "Values")
lines(data$Mes,
      data$Predicho,
      type = "l",
      col = 2)
legend("topright",                     
       c("Observado", "Predicho"),
       lty = 1,
       col = 1:2)
write.xlsx(data,"Resultados/Pronosticos_1_TAR_ISE_spread.xlsx",overwrite = T)


###########Pronósticos dos pasos adelante

### CORRIDA PARA OBTENER PRON?STICOS
LH=2
Iteration=20000
Burnin=8000
step.thv<-0.0525
d0=3
AA<-matrix(NA,nrow=8, ncol=LH)

for (i in 0:7) {
  set.seed(525)
  Datos=read.xlsx("Desempleo.xlsx")
  Datos=Datos[1:(168+(2*i)),]
  ISE=ts(Datos$ISE_estacional,start = c(2005,1),freq=12)
  Xt=diff(log(ISE))*100
  Xt=ts(Xt,start=c(2005,2),freq=12)
  TIB=read.xlsx("TIB.xlsx",startRow = 7,detectDates = T)
  TIB$Fecha=as.Date(TIB$`Fecha(dd/mm/aaaa)`)
  TIB$Año=as.numeric(format(TIB$Fecha,'%Y'))
  TIB$Mes=as.numeric(format(TIB$Fecha,'%m'))
  
  TIB_mensual=TIB%>%group_by(Año,Mes)%>%summarise(TIB=mean(`TIB.(Efectiva.anual).%`,na.rm=T))
  TIB_mensual=TIB_mensual[119:(286+(2*i)),]
  
  TES=read.xlsx("TES_mensual.xlsx",startRow = 7,detectDates = T)
  TES$`Año(aaaa)-Mes(mm)`=as.Date(TES$`Año(aaaa)-Mes(mm)`)
  TES=TES[(37-(2*i)):204,]
  class(TES$`Año(aaaa)-Mes(mm)`)
  
  TES$Año=as.numeric(format(TES$`Año(aaaa)-Mes(mm)`,'%Y'))
  TES$Mes=as.numeric(format(TES$`Año(aaaa)-Mes(mm)`,'%m'))
  TES_mensual=TES%>%group_by(Año,Mes)%>%summarise(TES=mean(`Tasa.a.10.años.%`))
  
  Datos=as.data.frame(cbind(TES_mensual$TES,TIB_mensual$TIB))
  names(Datos)=c("TES","TIB")
  Datos$spread=Datos$TES-Datos$TIB
  
  Spread=ts(Datos$spread,start = c(2005,1),freq=12)
  
  
  Zt=diff(Spread,lag=1)
  x2=Xt
  thresVar2=Zt
  p=pronosticos(LH, x2, thresVar2, Iteration, Burnin, step.thv, d0)
  px=p$seriex
  pz=p$seriez
  AA[i+1,]= t(tar.summarymedia(px))
}




CC<-matrix(NA,nrow=15, ncol=1)
CC[1,]=AA[1,1]  
CC[2,]=AA[1,2]  
CC[3,]=AA[2,1]  
CC[4,]=AA[2,2]  
CC[5,]=AA[3,1]  
CC[6,]=AA[3,2]  
CC[7,]=AA[4,1]  
CC[8,]=AA[4,2]  
CC[9,]=AA[5,1]  
CC[10,]=AA[5,2]  
CC[11,]=AA[6,1]  
CC[12,]=AA[6,2]  
CC[13,]=AA[7,1]
CC[14,]=AA[7,2]
CC[15,]=AA[8,1]



Pronostico=ts(CC[,1],start=c(2019,1),freq=12)
Comparacion=read.xlsx("Desempleo.xlsx")
Comparacion=Comparacion[168:183,]
Comp_des=ts(Comparacion$ISE_estacional,start = c(2018,12),freq=12)
Comp_des=diff(log(Comp_des))*100
par(mfrow=c(1,1))


data=as.data.frame(as.yearmon(time(Comp_des)))
names(data)="Mes"
data$Obsevado=Comp_des
data$Predicho=Pronostico

data$Mes
plot(data$Mes,
     data$Obsevado,
     type = "l",
     col = 1,
     xlab = "Year",
     ylab = "Values")
lines(data$Mes,
      data$Predicho,
      type = "l",
      col = 2)
legend("topright",                     
       c("Observado", "Predicho"),
       lty = 1,
       col = 1:2)
write.xlsx(data,"Resultados/Pronosticos_2_TAR_ISE_spread.xlsx",overwrite = T)

###########Pronósticos tres pasos adelante

### CORRIDA PARA OBTENER PRON?STICOS
LH=3
Iteration=20000
Burnin=8000
step.thv<-0.0525
d0=3
AA<-matrix(NA,nrow=5, ncol=LH)

for (i in 0:4) {
  set.seed(525)
  Datos=read.xlsx("Desempleo.xlsx")
  Datos=Datos[1:(168+(3*i)),]
  ISE=ts(Datos$ISE_estacional,start = c(2005,1),freq=12)
  Xt=diff(log(ISE))*100
  Xt=ts(Xt,start=c(2005,2),freq=12)
  TIB=read.xlsx("TIB.xlsx",startRow = 7,detectDates = T)
  TIB$Fecha=as.Date(TIB$`Fecha(dd/mm/aaaa)`)
  TIB$Año=as.numeric(format(TIB$Fecha,'%Y'))
  TIB$Mes=as.numeric(format(TIB$Fecha,'%m'))
  
  TIB_mensual=TIB%>%group_by(Año,Mes)%>%summarise(TIB=mean(`TIB.(Efectiva.anual).%`,na.rm=T))
  TIB_mensual=TIB_mensual[119:(286+(3*i)),]
  
  TES=read.xlsx("TES_mensual.xlsx",startRow = 7,detectDates = T)
  TES$`Año(aaaa)-Mes(mm)`=as.Date(TES$`Año(aaaa)-Mes(mm)`)
  TES=TES[(37-(3*i)):204,]
  class(TES$`Año(aaaa)-Mes(mm)`)
  
  TES$Año=as.numeric(format(TES$`Año(aaaa)-Mes(mm)`,'%Y'))
  TES$Mes=as.numeric(format(TES$`Año(aaaa)-Mes(mm)`,'%m'))
  TES_mensual=TES%>%group_by(Año,Mes)%>%summarise(TES=mean(`Tasa.a.10.años.%`))
  
  Datos=as.data.frame(cbind(TES_mensual$TES,TIB_mensual$TIB))
  names(Datos)=c("TES","TIB")
  Datos$spread=Datos$TES-Datos$TIB
  
  Spread=ts(Datos$spread,start = c(2005,1),freq=12)
  
  
  Zt=diff(Spread,lag=1)
  x2=Xt
  thresVar2=Zt
  p=pronosticos(LH, x2, thresVar2, Iteration, Burnin, step.thv, d0)
  px=p$seriex
  pz=p$seriez
  AA[i+1,]= t(tar.summarymedia(px))
}


CC<-matrix(NA,nrow=15, ncol=1)
CC[1,]=AA[1,1]  
CC[2,]=AA[1,2]  
CC[3,]=AA[1,3]  
CC[4,]=AA[2,1]  
CC[5,]=AA[2,2]  
CC[6,]=AA[2,3]  
CC[7,]=AA[3,1]  
CC[8,]=AA[3,2]  
CC[9,]=AA[3,3]  
CC[10,]=AA[4,1]  
CC[11,]=AA[4,2]  
CC[12,]=AA[4,3]
CC[13,]=AA[5,1]
CC[14,]=AA[5,2]
CC[15,]=AA[5,3]



Pronostico=ts(CC[,1],start(2019,1),freq=12)
Comparacion=read.xlsx("Desempleo.xlsx")
Comparacion=Comparacion[168:183,]
Comp_des=ts(Comparacion$ISE_estacional,start = c(2018,12),freq=12)
Comp_des=diff(log(Comp_des))*100
par(mfrow=c(1,1))


data=as.data.frame(as.yearmon(time(Comp_des)))
names(data)="Mes"
data$Obsevado=Comp_des
data$Predicho=Pronostico

data$Mes
plot(data$Mes,
     data$Obsevado,
     type = "l",
     col = 1,
     xlab = "Year",
     ylab = "Values")
lines(data$Mes,
      data$Predicho,
      type = "l",
      col = 2)
legend("topright",                     
       c("Observado", "Predicho"),
       lty = 1,
       col = 1:2)
write.xlsx(data,"Resultados/Pronosticos_3_TAR_ISE_spread.xlsx",overwrite = T)


###########Pronósticos cuatro pasos adelante

### CORRIDA PARA OBTENER PRON?STICOS
LH=4
Iteration=20000
Burnin=8000
step.thv<-0.132
d0=2
AA<-matrix(NA,nrow=4, ncol=LH)

for (i in 0:3) {
  set.seed(525)
  Datos=read.xlsx("Desempleo.xlsx")
  Datos=Datos[1:(168+(4*i)),]
  ISE=ts(Datos$ISE_estacional,start = c(2005,1),freq=12)
  Xt=diff(log(ISE))*100
  Xt=ts(Xt,start=c(2005,2),freq=12)
  TIB=read.xlsx("TIB.xlsx",startRow = 7,detectDates = T)
  TIB$Fecha=as.Date(TIB$`Fecha(dd/mm/aaaa)`)
  TIB$Año=as.numeric(format(TIB$Fecha,'%Y'))
  TIB$Mes=as.numeric(format(TIB$Fecha,'%m'))
  
  TIB_mensual=TIB%>%group_by(Año,Mes)%>%summarise(TIB=mean(`TIB.(Efectiva.anual).%`,na.rm=T))
  TIB_mensual=TIB_mensual[119:(286+(4*i)),]
  
  TES=read.xlsx("TES_mensual.xlsx",startRow = 7,detectDates = T)
  TES$`Año(aaaa)-Mes(mm)`=as.Date(TES$`Año(aaaa)-Mes(mm)`)
  TES=TES[(37-(4*i)):204,]
  class(TES$`Año(aaaa)-Mes(mm)`)
  
  TES$Año=as.numeric(format(TES$`Año(aaaa)-Mes(mm)`,'%Y'))
  TES$Mes=as.numeric(format(TES$`Año(aaaa)-Mes(mm)`,'%m'))
  TES_mensual=TES%>%group_by(Año,Mes)%>%summarise(TES=mean(`Tasa.a.10.años.%`))
  
  Datos=as.data.frame(cbind(TES_mensual$TES,TIB_mensual$TIB))
  names(Datos)=c("TES","TIB")
  Datos$spread=Datos$TES-Datos$TIB
  
  Spread=ts(Datos$spread,start = c(2005,1),freq=12)
  
  
  Zt=diff(Spread,lag=1)
  x2=Xt
  thresVar2=Zt
  p=pronosticos(LH, x2, thresVar2, Iteration, Burnin, step.thv, d0)
  px=p$seriex
  pz=p$seriez
  AA[i+1,]= t(tar.summarymedia(px))
}


CC<-matrix(NA,nrow=15, ncol=1)
CC[1,]=AA[1,1]  
CC[2,]=AA[1,2]  
CC[3,]=AA[1,3]  
CC[4,]=AA[1,4]  
CC[5,]=AA[2,1]  
CC[6,]=AA[2,2]  
CC[7,]=AA[2,3]  
CC[8,]=AA[2,4]  
CC[9,]=AA[3,1]  
CC[10,]=AA[3,2]  
CC[11,]=AA[3,3]  
CC[12,]=AA[3,4]  
CC[13,]=AA[4,1]
CC[14,]=AA[4,2]
CC[15,]=AA[4,3]


Pronostico=ts(CC[,1],start(2019,1),freq=12)
Comparacion=read.xlsx("Desempleo.xlsx")
Comparacion=Comparacion[168:183,]
Comp_des=ts(Comparacion$ISE_estacional,start = c(2018,12),freq=12)
Comp_des=diff(log(Comp_des))*100
par(mfrow=c(1,1))


data=as.data.frame(as.yearmon(time(Comp_des)))
names(data)="Mes"
data$Obsevado=Comp_des
data$Predicho=Pronostico

data$Mes
plot(data$Mes,
     data$Obsevado,
     type = "l",
     col = 1,
     xlab = "Year",
     ylab = "Values")
lines(data$Mes,
      data$Predicho,
      type = "l",
      col = 2)
legend("topright",                     
       c("Observado", "Predicho"),
       lty = 1,
       col = 1:2)
write.xlsx(data,"Resultados/Pronosticos_4_TAR_ISE_spread.xlsx",overwrite = T)

######################## SAR

setwd("D:/sarbelaez/Documents/Maestría/Tesis/Datos finales")

Datos=read.xlsx("Desempleo.xlsx")
ISE=ts(Datos$ISE_estacional[1:168],start = c(2005,1),freq=12)

Xt=diff(log(ISE))*100
plot(armasubsets(Xt,nar=30,nma=0))
Modelo_ar=stats::arima(Xt,order=c(2,0,0),seasonal=c(2,0,0),include.mean = F)
coeftest(Modelo_ar)
summary(Modelo_ar)
par(mfrow=c(2,1))
plot(Modelo_ar$residuals,ylab="Residuales", xlab="Tiempo")
hist(Modelo_ar$residuals,main="Histograma de residuales estandarizados",ylab="Residuales")
jarque.bera.test(Modelo_ar$residuals)
par(mfrow=c(2,2))
acf(Modelo_ar$residuals, main="I",xlab="Tiempo",lag.max=50)        # función de autocorrelación muestral
pacf(Modelo_ar$residuals, main="II",xlab="Tiempo",ylab="PACF",lag.max=50)       # función de autocorrelación parcial muestral
par(mfrow=c(1,1))
B=matrix(NA,nrow=36,ncol=1)
for (i in 1:36) {
  A=Box.test(Modelo_ar$residuals, lag = i, type = "Ljung-Box")
  B[i,1]=A$p.value
}
# Prueba CUSUM y CUSUM-SQ para los residuales del modelo (evidencia de una especifi
#cación correcta o no del modelo y heterocedasticidad, resp.)
par(mfrow=c(2,1))
cum=cumsum(Modelo_ar$residuals)/sd(Modelo_ar$residuals)
N=length(Modelo_ar$residuals)
cumq=cumsum(Modelo_ar$residuals^2)/sum(Modelo_ar$residuals^2)
Af=0.948 ###Cuantil del 95% para la estad?stica cusum
co=0.12672####Valor del cuantil aproximado para cusumsq para n/2
LS=Af*sqrt(N)+2*Af*c(1:length(Modelo_ar$residuals))/sqrt(N)
LI=-LS
LQS=co+(1:length(Modelo_ar$residuals))/N
LQI=-co+(1:length(Modelo_ar$residuals))/N
plot(cum,type="l",ylim=c(min(LI),max(LS)),xlab="Tiempo",ylab="CUSUM",main="III")
lines(LS,type="S",col="black")
lines(LI,type="S",col="black")
#CUSUMSQ
plot(cumq,type="l",xlab="Tiempo",ylab="CUSUMSQ",main="IV")                      
lines(LQS,type="S",col="black")                                                                           
lines(LQI,type="S",col="black")


###Ponósticos 1 paso adelante
AA=matrix(NA,nrow=15,ncol=1)

for (i in 0:14) {
  set.seed(525)
  Datos=read.xlsx("Desempleo.xlsx")
  Datos=Datos[1:(168+(i)),]
  ISE=ts(Datos$ISE_estacional,start = c(2005,1),freq=12)
  Xt=diff(log(ISE))*100
  refit=Arima(Xt,order=c(2,0,0),seasonal=c(2,0,0),include.mean = FALSE,model=Modelo_ar)
  AA[i+1,]=t(forecast(refit,h=1)$mean)
}

AA
Pronostico=matrix(NA,nrow=15,ncol=1)
Comparacion=read.xlsx("Desempleo.xlsx")
Pronostico[1:15,1]=AA[,1]
Pronostico=ts(Pronostico,start=c(2019,1),freq=12)

Comparacion=Comparacion[168:183,]
Comp_des=ts(Comparacion$ISE_estacional,start = c(2018,12),freq=12)
Comp_des=diff(log(Comp_des))*100
par(mfrow=c(1,1))


data=as.data.frame(as.yearmon(time(Comp_des)))
names(data)="Mes"
data$Obsevado=Comp_des
data$Predicho=Pronostico

data$Mes
plot(data$Mes,
     data$Obsevado,
     type = "l",
     col = 1,
     xlab = "Year",
     ylab = "Values")
lines(data$Mes,
      data$Predicho,
      type = "l",
      col = 2)
legend("topright",                     
       c("Observado", "Predicho"),
       lty = 1,
       col = 1:2)

write.xlsx(data,"Resultados/Pronosticos_1_AR_ISE_spread.xlsx",overwrite = T)

###Ponósticos 2 pasos adelante
AA=matrix(NA,nrow=8,ncol=2)

for (i in 0:7) {
  set.seed(525)
  Datos=read.xlsx("Desempleo.xlsx")
  Datos=Datos[1:(168+(2*i)),]
  ISE=ts(Datos$ISE_estacional,start = c(2005,1),freq=12)
  Xt=diff(log(ISE))*100
  refit=Arima(Xt,order=c(2,0,0),seasonal=c(2,0,0),include.mean = FALSE,model=Modelo_ar)
  AA[i+1,]=t(forecast(refit,h=2)$mean)
}

CC<-matrix(NA,nrow=15, ncol=1)
CC[1,]=AA[1,1]  
CC[2,]=AA[1,2]  
CC[3,]=AA[2,1]  
CC[4,]=AA[2,2]  
CC[5,]=AA[3,1]  
CC[6,]=AA[3,2]  
CC[7,]=AA[4,1]  
CC[8,]=AA[4,2]  
CC[9,]=AA[5,1]  
CC[10,]=AA[5,2]  
CC[11,]=AA[6,1]  
CC[12,]=AA[6,2]  
CC[13,]=AA[7,1]
CC[14,]=AA[7,2]
CC[15,]=AA[8,1]

Pronostico=matrix(NA,nrow=15,ncol=1)
Comparacion=read.xlsx("Desempleo.xlsx")
Pronostico[1:15,1]=CC[,1]
Pronostico=ts(Pronostico,start=c(2019,1),freq=12)

Comparacion=Comparacion[168:183,]
Comp_des=ts(Comparacion$ISE_estacional,start = c(2018,12),freq=12)
Comp_des=diff(Comp_des)
par(mfrow=c(1,1))


data=as.data.frame(as.yearmon(time(Comp_des)))
names(data)="Mes"
data$Obsevado=Comp_des
data$Predicho=Pronostico

data$Mes
plot(data$Mes,
     data$Obsevado,
     type = "l",
     col = 1,
     xlab = "Year",
     ylab = "Values")
lines(data$Mes,
      data$Predicho,
      type = "l",
      col = 2)
legend("topright",                     
       c("Observado", "Predicho"),
       lty = 1,
       col = 1:2)

write.xlsx(data,"Resultados/Pronosticos_2_AR_ISE_spread.xlsx",overwrite = T)



###Ponósticos 3 pasos adelante
AA=matrix(NA,nrow=5,ncol=3)

for (i in 0:4) {
  set.seed(525)
  Datos=read.xlsx("Desempleo.xlsx")
  Datos=Datos[1:(168+(3*i)),]
  ISE=ts(Datos$ISE_estacional,start = c(2005,1),freq=12)
  Xt=diff(log(ISE))*100
  refit=Arima(Xt,order=c(2,0,0),seasonal=c(2,0,0),include.mean = FALSE,model=Modelo_ar)
  AA[i+1,]=t(forecast(refit,h=3)$mean)
}

CC<-matrix(NA,nrow=15, ncol=1)
CC[1,]=AA[1,1]  
CC[2,]=AA[1,2]  
CC[3,]=AA[1,3]  
CC[4,]=AA[2,1]  
CC[5,]=AA[2,2]  
CC[6,]=AA[2,3]  
CC[7,]=AA[3,1]  
CC[8,]=AA[3,2]  
CC[9,]=AA[3,3]  
CC[10,]=AA[4,1]  
CC[11,]=AA[4,2]  
CC[12,]=AA[4,3]  
CC[13,]=AA[5,1]
CC[14,]=AA[5,2]
CC[15,]=AA[5,3]

Pronostico=matrix(NA,nrow=15,ncol=1)
Comparacion=read.xlsx("Desempleo.xlsx")
Pronostico[1:15,1]=CC[,1]
Pronostico=ts(Pronostico,start=c(2019,1),freq=12)

Comparacion=Comparacion[168:183,]
Comp_des=ts(Comparacion$ISE_estacional,start = c(2018,12),freq=12)
Comp_des=diff(log(Comp_des))*100
par(mfrow=c(1,1))


data=as.data.frame(as.yearmon(time(Comp_des)))
names(data)="Mes"
data$Obsevado=Comp_des
data$Predicho=Pronostico

data$Mes
plot(data$Mes,
     data$Obsevado,
     type = "l",
     col = 1,
     xlab = "Year",
     ylab = "Values")
lines(data$Mes,
      data$Predicho,
      type = "l",
      col = 2)
legend("topright",                     
       c("Observado", "Predicho"),
       lty = 1,
       col = 1:2)

write.xlsx(data,"Resultados/Pronosticos_3_AR_ISE_spread.xlsx",overwrite = T)

###Ponósticos 4 pasos adelante
AA=matrix(NA,nrow=4,ncol=4)

for (i in 0:3) {
  set.seed(525)
  Datos=read.xlsx("Desempleo.xlsx")
  Datos=Datos[1:(168+(4*i)),]
  ISE=ts(Datos$ISE_estacional,start = c(2005,1),freq=12)
  Xt=diff(log(ISE))*100
  refit=Arima(Xt,order=c(2,0,0),seasonal=c(2,0,0),include.mean = FALSE,model=Modelo_ar)
  AA[i+1,]=t(forecast(refit,h=4)$mean)
}

CC<-matrix(NA,nrow=15, ncol=1)
CC[1,]=AA[1,1]  
CC[2,]=AA[1,2]  
CC[3,]=AA[1,3]  
CC[4,]=AA[1,4]  
CC[5,]=AA[2,1]  
CC[6,]=AA[2,2]  
CC[7,]=AA[2,3]  
CC[8,]=AA[2,4]  
CC[9,]=AA[3,1]  
CC[10,]=AA[3,2]  
CC[11,]=AA[3,3]  
CC[12,]=AA[3,4]  
CC[13,]=AA[4,1]
CC[14,]=AA[4,2]
CC[15,]=AA[4,3]

Pronostico=matrix(NA,nrow=15,ncol=1)
Comparacion=read.xlsx("Desempleo.xlsx")
Pronostico[1:15,1]=CC[,1]
Pronostico=ts(Pronostico,start=c(2019,1),freq=12)

Comparacion=Comparacion[168:183,]
Comp_des=ts(Comparacion$ISE_estacional,start = c(2018,12),freq=12)
Comp_des=diff(log(Comp_des))*100
par(mfrow=c(1,1))


data=as.data.frame(as.yearmon(time(Comp_des)))
names(data)="Mes"
data$Obsevado=Comp_des
data$Predicho=Pronostico

data$Mes
plot(data$Mes,
     data$Obsevado,
     type = "l",
     col = 1,
     xlab = "Year",
     ylab = "Values")
lines(data$Mes,
      data$Predicho,
      type = "l",
      col = 2)
legend("topright",                     
       c("Observado", "Predicho"),
       lty = 1,
       col = 1:2)

write.xlsx(data,"Resultados/Pronosticos_4_AR_ISE_spread.xlsx",overwrite = T)

#Suavizamiento 
Datos=read.xlsx("Desempleo.xlsx")
Datos=Datos[1:168,]
ISE=ts(Datos$ISE_estacional,start = c(2005,1),freq=12)
Xt=diff(log(ISE))*100

exponencial=ets(Xt,model = "ZNZ")
summary(exponencial)
plot(exponencial)
par(mfrow=c(2,1))
plot(exponencial$residuals,ylab="Residuales", xlab="Tiempo")
hist(exponencial$residuals,main="Histograma de residuales estandarizados",ylab="Residuales")
jarque.bera.test(exponencial$residuals)
par(mfrow=c(2,2))
acf(exponencial$residuals, main="I",xlab="Tiempo",lag.max=50)        # función de autocorrelación muestral
pacf(exponencial$residuals, main="II",xlab="Tiempo",ylab="PACF",lag.max=50)       # función de autocorrelación parcial muestral
par(mfrow=c(1,1))
B=matrix(NA,nrow=36,ncol=1)
for (i in 1:36) {
  A=Box.test(exponencial$residuals, lag = i, type = "Ljung-Box")
  B[i,1]=A$p.value
}
# Prueba CUSUM y CUSUM-SQ para los residuales del modelo (evidencia de una especifi
#cación correcta o no del modelo y heterocedasticidad, resp.)
par(mfrow=c(2,1))
cum=cumsum(exponencial$residuals)/sd(exponencial$residuals)
N=length(exponencial$residuals)
cumq=cumsum(exponencial$residuals^2)/sum(exponencial$residuals^2)
Af=0.948 ###Cuantil del 95% para la estad?stica cusum
co=0.12672####Valor del cuantil aproximado para cusumsq para n/2
LS=Af*sqrt(N)+2*Af*c(1:length(exponencial$residuals))/sqrt(N)
LI=-LS
LQS=co+(1:length(exponencial$residuals))/N
LQI=-co+(1:length(exponencial$residuals))/N
plot(cum,type="l",ylim=c(min(LI),max(LS)),xlab="Tiempo",ylab="CUSUM",main="III")
lines(LS,type="S",col="black")
lines(LI,type="S",col="black")
#CUSUMSQ
plot(cumq,type="l",xlab="Tiempo",ylab="CUSUMSQ",main="IV")                      
lines(LQS,type="S",col="black")                                                                           
lines(LQI,type="S",col="black")


###Ponósticos 1 paso adelante
AA=matrix(NA,nrow=15,ncol=1)


for (i in 0:14) {
  set.seed(525)
  Datos=read.xlsx("Desempleo.xlsx")
  Datos=Datos[1:(168+(i)),]
  ISE=ts(Datos$ISE_estacional,start = c(2005,1),freq=12)
  Xt=diff(log(ISE))*100
  refit=ets(Xt,model=exponencial,use.initial.values = T)
  AA[i+1,]=forecast(refit,h=1)$mean
}

AA
Pronostico=ts(AA[,1],start=c(2019,1),freq=12)
Comparacion=read.xlsx("Desempleo.xlsx")
Comparacion=Comparacion[168:183,]
Comp_des=ts(Comparacion$ISE_estacional,start = c(2018,12),freq=12)
Comp_des=diff(log(Comp_des))*100
par(mfrow=c(1,1))


data=as.data.frame(as.yearmon(time(Comp_des)))
names(data)="Mes"
data$Obsevado=Comp_des
data$Predicho=Pronostico

data$Mes
plot(data$Mes,
     data$Obsevado,
     type = "l",
     col = 1,
     xlab = "Year",
     ylab = "Values")
lines(data$Mes,
      data$Predicho,
      type = "l",
      col = 2)
legend("topright",                     
       c("Observado", "Predicho"),
       lty = 1,
       col = 1:2)

write.xlsx(data,"Resultados/Pronosticos_1_EXP_ISE_spread.xlsx",overwrite = T)

###Ponósticos 2 pasos adelante
AA=matrix(NA,nrow=8,ncol=2)

for (i in 0:7) {
  set.seed(525)
  Datos=read.xlsx("Desempleo.xlsx")
  Datos=Datos[1:(168+(2*i)),]
  ISE=ts(Datos$ISE_estacional,start = c(2005,1),freq=12)
  Xt=diff(log(ISE))*100
  refit=ets(Xt,model=exponencial,use.initial.values = T)
  AA[i+1,]=t(forecast(refit,h=2)$mean)
}

CC<-matrix(NA,nrow=15, ncol=1)
CC[1,]=AA[1,1]  
CC[2,]=AA[1,2]  
CC[3,]=AA[2,1]  
CC[4,]=AA[2,2]  
CC[5,]=AA[3,1]  
CC[6,]=AA[3,2]  
CC[7,]=AA[4,1]  
CC[8,]=AA[4,2]  
CC[9,]=AA[5,1]  
CC[10,]=AA[5,2]  
CC[11,]=AA[6,1]  
CC[12,]=AA[6,2]  
CC[13,]=AA[7,1]
CC[14,]=AA[7,2]
CC[15,]=AA[8,1]

Pronostico=ts(CC[,1],start=c(2019,1),freq=12)
Comparacion=read.xlsx("Desempleo.xlsx")
Comparacion=Comparacion[168:183,]
Comp_des=ts(Comparacion$ISE_estacional,start = c(2018,12),freq=12)
Comp_des=diff(Comp_des)
par(mfrow=c(1,1))


data=as.data.frame(as.yearmon(time(Comp_des)))
names(data)="Mes"
data$Obsevado=Comp_des
data$Predicho=Pronostico

data$Mes
plot(data$Mes,
     data$Obsevado,
     type = "l",
     col = 1,
     xlab = "Year",
     ylab = "Values")
lines(data$Mes,
      data$Predicho,
      type = "l",
      col = 2)
legend("topright",                     
       c("Observado", "Predicho"),
       lty = 1,
       col = 1:2)

write.xlsx(data,"Resultados/Pronosticos_2_EXP_ISE_spread.xlsx",overwrite = T)



###Ponósticos 3 pasos adelante
AA=matrix(NA,nrow=5,ncol=3)

for (i in 0:4) {
  set.seed(525)
  Datos=read.xlsx("Desempleo.xlsx")
  Datos=Datos[1:(168+(3*i)),]
  ISE=ts(Datos$ISE_estacional,start = c(2005,1),freq=12)
  Xt=diff(log(ISE))*100
  refit=ets(Xt,model=exponencial,use.initial.values = T)
  AA[i+1,]=t(forecast(refit,h=3)$mean)
}

CC<-matrix(NA,nrow=15, ncol=1)
CC[1,]=AA[1,1]  
CC[2,]=AA[1,2]  
CC[3,]=AA[1,3]  
CC[4,]=AA[2,1]  
CC[5,]=AA[2,2]  
CC[6,]=AA[2,3]  
CC[7,]=AA[3,1]  
CC[8,]=AA[3,2]  
CC[9,]=AA[3,3]  
CC[10,]=AA[4,1]  
CC[11,]=AA[4,2]  
CC[12,]=AA[4,3]  
CC[13,]=AA[5,1]
CC[14,]=AA[5,2]
CC[15,]=AA[5,3]

Pronostico=ts(CC[,1],start=c(2019,1),freq=12)
Comparacion=read.xlsx("Desempleo.xlsx")
Comparacion=Comparacion[168:183,]
Comp_des=ts(Comparacion$ISE_estacional,start = c(2018,12),freq=12)
Comp_des=diff(Comp_des)
par(mfrow=c(1,1))


data=as.data.frame(as.yearmon(time(Comp_des)))
names(data)="Mes"
data$Obsevado=Comp_des
data$Predicho=Pronostico

data$Mes
plot(data$Mes,
     data$Obsevado,
     type = "l",
     col = 1,
     xlab = "Year",
     ylab = "Values")
lines(data$Mes,
      data$Predicho,
      type = "l",
      col = 2)
legend("topright",                     
       c("Observado", "Predicho"),
       lty = 1,
       col = 1:2)

write.xlsx(data,"Resultados/Pronosticos_3_EXP_ISE_spread.xlsx",overwrite = T)

###Ponósticos 4 pasos adelante
AA=matrix(NA,nrow=4,ncol=4)

for (i in 0:3) {
  set.seed(525)
  Datos=read.xlsx("Desempleo.xlsx")
  Datos=Datos[1:(168+(4*i)),]
  ISE=ts(Datos$ISE_estacional,start = c(2005,1),freq=12)
  Xt=diff(log(ISE))*100
  refit=ets(Xt,model=exponencial,use.initial.values = T)
  AA[i+1,]=t(forecast(refit,h=4)$mean)
}

CC<-matrix(NA,nrow=15, ncol=1)
CC[1,]=AA[1,1]  
CC[2,]=AA[1,2]  
CC[3,]=AA[1,3]  
CC[4,]=AA[1,4]  
CC[5,]=AA[2,1]  
CC[6,]=AA[2,2]  
CC[7,]=AA[2,3]  
CC[8,]=AA[2,4]  
CC[9,]=AA[3,1]  
CC[10,]=AA[3,2]  
CC[11,]=AA[3,3]  
CC[12,]=AA[3,4]  
CC[13,]=AA[4,1]
CC[14,]=AA[4,2]
CC[15,]=AA[4,3]

Pronostico=ts(CC[,1],start=c(2019,1),freq=12)
Comparacion=read.xlsx("Desempleo.xlsx")
Comparacion=Comparacion[168:183,]
Comp_des=ts(Comparacion$ISE_estacional,start = c(2018,12),freq=12)
Comp_des=diff(Comp_des)
par(mfrow=c(1,1))


data=as.data.frame(as.yearmon(time(Comp_des)))
names(data)="Mes"
data$Obsevado=Comp_des
data$Predicho=Pronostico

data$Mes
plot(data$Mes,
     data$Obsevado,
     type = "l",
     col = 1,
     xlab = "Year",
     ylab = "Values")
lines(data$Mes,
      data$Predicho,
      type = "l",
      col = 2)
legend("topright",                     
       c("Observado", "Predicho"),
       lty = 1,
       col = 1:2)

write.xlsx(data,"Resultados/Pronosticos_4_EXP_ISE_spread.xlsx",overwrite = T)
