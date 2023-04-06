rm(list= ls())

#Cargando librerías

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
library(FitAR)

#Se programan los modelos de 1 a 3 regímenes para definir cuál es el más apropiado

#################### INICIO DEL PROGRAMA 1 REGÍMEN




####################  Estimación de los coeficientes autorregresivos y exógenos      
########################    are.coeffxph


are.coeffxph=function(ay, p, P, q, sig, mu0ph, v0ph, PH, qh, lagp1, lagP1, lagq1, constant, thresVar, s) 
{
  P11 <- max(max(lagp1)+s*max(lagP1), max(lagq1)) 
  n <- length(ay)
  yt <- ay[(P11 + 1):n]
  xxx.1<-vector("list",P)
  txxx.1<-vector("list",P)
  PH.1<-matrix(PH, nrow=P, ncol=1)
  qh.1<-matrix(qh, nrow=q, ncol=1)
  
  L<-matrix(NA, nrow=P, ncol=(n-P11))
  Q<-matrix(NA, nrow=q, ncol=(n-P11))
  xx.1 <- matrix(NA, nrow = p, ncol = (n-P11))
  for (j in 1:P){
    xxx.1[[j]]<-matrix(NA, nrow = p, ncol = (n-P11))
  }
  for (j in 1:P){
    txxx.1[[j]]<-matrix(NA, nrow =(n-P11), ncol =p )
  }
  
  for (i in 1:p){
    xx.1[i, ] <- ay[(P11-lagp1[i]+1):(n-lagp1[i])]
  }
  txx.1<-t(xx.1)
  for (j in 1:P){
    for (i in 1:p) {
      xxx.1[[j]][i,] <- ay[(P11-lagp1[i]-lagP1[j]*s+1):(n-lagp1[i]-lagP1[j]*s)]*PH[j]
    }
  }
  for (j in 1:P) {
    txxx.1[[j]]<-t(xxx.1[[j]])
  }
  auxsuma<-matrix(0, nrow=nrow(txxx.1[[1]]) , ncol=p)
  for (k in 1:P){
    auxsuma<-auxsuma+txxx.1[[k]]
  }
  x.1t<-txx.1-auxsuma
  x.1<-t(x.1t)
  
  
  if (constant==1){
    tx <- cbind(1,t(x.1))
  }
  else {
    tx<- t(x.1)
  }
  
  
  for (i in 1:P){
    L[i,]<-ay[(P11-lagP1[i]*s+1):(n-lagP1[i]*s)]
  }
  
  for (i in 1:q){
    Q[i,]<-thresVar[(P11-lagq1[i]+1):(n-lagq1[i])]
  }
  
  Ytt<-yt-(t(L)%*%PH.1+t(Q)%*%qh.1)
  Yt<-matrix(Ytt, ncol=1)
  sigma<-(t(tx)%*%tx)/sig + v0ph
  mu<-solve(sigma,(t(tx)%*%Yt)/sig + v0ph %*% mu0ph)
  ph<-rmvnorm(1,mu,solve(sigma),method = "chol")
  
  
  
  return(ph)
}

#################################################################
#################################################


####################  Estimación de los coeficientes autorregresivos y exógenos      
########################    are.coeffxPH


are.coeffxPH=function(ay, p, P, q, sig, mu0PH, v0PH, ph, qh, lagp1, lagP1, lagq1, constant, thresVar, s) 
{
  P11 <- max(max(lagp1)+s*max(lagP1), max(lagq1)) 
  n <- length(ay)
  yt <- ay[(P11 + 1):n]
  xxx.1<-vector("list",p)
  txxx.1<-vector("list",p)
  ph.1<-matrix(ph, nrow=p+constant, ncol=1)
  qh.1<-matrix(qh, nrow=q, ncol=1)
  
  L<-matrix(NA, nrow=p, ncol=(n-P11))
  Q<-matrix(NA, nrow=q, ncol=(n-P11))
  xx.1 <- matrix(NA, nrow = P, ncol = (n-P11))
  for (j in 1:p){
    xxx.1[[j]]<-matrix(NA, nrow = P, ncol = (n-P11))
  }
  for (j in 1:p){
    txxx.1[[j]]<-matrix(NA, nrow =(n-P11), ncol =P)
  }
  
  
  for (i in 1:P){
    xx.1[i, ] <- ay[(P11-lagP1[i]*s+1):(n-lagP1[i]*s)]
  }
  txx.1<-t(xx.1)
  for (j in 1:p){
    for (i in 1:P) {
      xxx.1[[j]][i,] <- ay[(P11-lagP1[i]*s-lagp1[j]+1):(n-lagP1[i]*s-lagp1[j])]*ph[j+constant]
    }
  }
  for (j in 1:p) {
    txxx.1[[j]]<-t(xxx.1[[j]])
  }
  auxsuma<-matrix(0, nrow=nrow(txxx.1[[1]]) , ncol=P)
  
  for (k in 1:p){
    auxsuma<-auxsuma+txxx.1[[k]]
  }
  tx<-txx.1-auxsuma
  
  for (i in 1:p){
    L[i,]<-ay[(P11-lagp1[i]+1):(n-lagp1[i])]
  }
  if (constant==1){
    L<-cbind(1,t(L))
  }
  else {
    L<-t(L)
  }
  for (i in 1:q){
    Q[i,]<-thresVar[(P11-lagq1[i]+1):(n-lagq1[i])]
  }
  
  Ytt<-yt-(L%*%ph.1+t(Q)%*%qh.1)
  Yt<-matrix(Ytt, ncol=1)
  sigma<-(t(tx)%*%tx)/sig + v0PH
  mu<-solve(sigma,(t(tx)%*%Yt)/sig + v0PH %*% mu0PH)
  PH<-rmvnorm(1,mu,solve(sigma),method = "chol")
  
  return(PH)
}

#################################################################
#################################################

####################  Estimación de los coeficientes autorregresivos y exógenos      
########################    are.coeffxqh


are.coeffxqh=function(ay, p, P, q, sig, mu0qh, v0qh, ph, PH, lagp1, lagP1, lagq1, constant, thresVar, s) 
{
  P11 <- max(max(lagp1)+s*max(lagP1), max(lagq1)) 
  n <- length(ay)
  yt <- ay[(P11 + 1):n]
  ph.1<-matrix(ph, nrow=p+constant, ncol=1)
  PH.1<-matrix(PH, nrow=P, ncol=1)
  A<-matrix(NA, nrow=P*(s-1), ncol=(n-P11))
  L<-matrix(NA, nrow=p, ncol=(n-P11))
  Q<-matrix(NA, nrow=P, ncol=(n-P11))
  x.1 <- matrix(NA, nrow = q, ncol = (n-P11))
  
  yy=vector("list", P)
  for (j in 1:P){
    yy[[j]]<-matrix(NA, nrow=(s-1), ncol=(n-P11))
  }
  coefaux<- matrix(NA, nrow = P*(s-1), ncol =1)
  xx=vector("list", P)
  for (j in 1:P){
    xx[[j]]<-matrix(NA, nrow=(s-1), ncol=1)
  }
  
  
  for (i in 1:P){
    
    xx[[i]][1:(s-p-1),]<-rep(0,(s-p-1))
    
    xx[[i]][(s-p):(s-1), ]<- -ph[(1+constant):(p+constant)]*PH[i]
    
  }
  
  for (j in 1:P){
    coefaux[((j-1)*(s-p-1)+(j-1)*p+1):(j*(s-p-1)+(j-1)*p),]<-xx[[j]][1:(s-p-1),] 
    coefaux[(j*(s-p-1)+(j-1)*p+1):(j*(s-p-1)+j*p),]<- xx[[j]][(s-p):(s-1), ]
  }
  
  for (i in 1:q){
    x.1[i, ] <- thresVar[(P11-lagq1[i]+1):(n-lagq1[i])]
  }
  tx<-t(x.1)
  
  for (i in 1:p){
    L[i,]<-ay[(P11-lagp1[i]+1):(n-lagp1[i])]
  }
  if (constant==1){
    L<-cbind(1,t(L))
  }
  else {
    L<-t(L)
  }
  
  for (i in 1:P){
    Q[i,]<-ay[(P11-lagP1[i]*s+1):(n-lagP1[i]*s)]
  }
  for (j in 1:P){
    for (i in 1:(s-p-1)){
      yy[[j]][i,]<-ay[(P11-((j-1)*s+p+i)+1):(n-((j-1)*s+p+i))]
    }
    for (k in (s-p-1+1):(s-1)){
      yy[[j]][k, ]<-ay[(P11-(j*s+ k-(s-p-1))+1):(n-(j*s+k-(s-p-1)))]
    }
  }
  for (j in 1:P){
    A[((j-1)*(s-p-1)+(j-1)*p+1):(j*(s-p-1)+(j-1)*p),]<- yy[[j]][1:(s-p-1),]
    A[(j*(s-p-1)+(j-1)*p+1):(j*(s-p-1)+j*p),]<- yy[[j]][(s-p-1+1):(s-1),]
  }
  
  
  Ytt<-yt-(t(A)%*%coefaux+L%*%ph.1+t(Q)%*%PH.1)
  Yt<-matrix(Ytt, ncol=1)
  sigma<-(t(tx)%*%tx)/sig + v0qh
  mu<-solve(sigma,(t(tx)%*%Yt)/sig + v0qh %*% mu0qh)
  qh<-rmvnorm(1,mu,solve(sigma),method = "chol")
  
  
  return(qh)
}

#################################################################
#################################################



############### Extraer la varianza de la distribuci?n de los errores      
##################  are.sigmax

are.sigmax=function(ay, p, P, q, ph, PH, qh, v, lambda, lagp1, lagP1, lagq1, constant, thresVar, s)
{
  P11 <- max(max(lagp1)+s*max(lagP1), max(lagq1)) 
  n <- length(ay)
  yt <- ay[(P11 + 1):n]
  x.1 <- matrix(0, nrow = p+s*P+q, ncol = (n - P11))
  x.11<-matrix(NA, nrow = p, ncol = (n-P11))
  x.12<-matrix(NA, nrow = P, ncol = (n-P11))
  x.13<-vector("list",P)
  for (j in 1:P){
    x.13[[j]]<-matrix(NA, nrow = p, ncol = (n-P11))
  }
  x.14<-matrix(NA, nrow = q, ncol = (n-P11))
  
  p.1<-matrix(0,nrow=p+s*P+q+constant,ncol=1)
  ph<-matrix(ph,nrow=p+constant,ncol=1)
  PH<-matrix(PH,nrow=P,ncol=1)
  qh<-matrix(qh, nrow=q,ncol=1)
  for (i in 1:(p+constant)){
    p.1[i]<-ph[i]
  }
  for (i in 1:P){
    p.1[i*s+constant]<-PH[i]
  }
  for (i in 1:P){
    for (j in 1:p){
      p.1[i*s+j+constant]<- -ph[j+constant]*PH[i]
    }
  }
  for (i in 1:q){
    p.1[p+s*P+constant+i]<-qh[i]
  }
  
  y<- matrix(yt, ncol = 1)
  for (i in 1:p){
    x.11[i,]<-ay[(P11 - lagp1[i] + 1):(n - lagp1[i])] 
  }
  x.1[1:p,]<-x.11
  for (i in 1:P){
    x.12[i,]<-ay[(P11 - lagP1[i]*s + 1):(n - lagP1[i]*s)]
  }
  x.1[seq(s,P*s,s),]<-x.12
  for (i in 1:P){
    for (j in 1:p){
      x.13[[i]][j,]<-ay[(P11 - (lagp1[j]+s*lagP1[i]) + 1):(n -(lagp1[j]+s*lagP1[i]))]
    }
  }
  for (i in 1:P){ 
    x.1[seq(i*s+1,i*s+p,1),]<-x.13[[i]]
  }
  for (i in 1:q) {
    x.14[i, ] <- thresVar[(P11 - lagq1[i] + 1):(n - lagq1[i])]
  }
  x.1[(p+s*P+1):(p+s*P+q),]<-x.14
  if (constant == 1) {
    tx <- cbind(1, t(x.1))
  }
  else {
    tx <- t(x.1)
  }
  s2 <- (t(y-tx%*%p.1)%*%(y-tx%*%p.1))/n
  
  shape <- (v + n)/2
  rate <- (v*lambda + n*s2)/2
  sigma <- 1/rgamma(1, shape, rate)
  return(sigma)
}

#############################################################################
##########################################


###################### calcular la función log.verosimil       
############################ are.likx

are.likx=function(ay, p1, P1, q1, ph.1, PH.1, qh.1, sig.1, lagp1, lagP1, lagq1,  constant, thresVar, s) 
  
{
  P11 <- max(max(lagp1)+s*max(lagP1), max(lagq1)) 
  n <- length(ay)
  yt <- ay[(P11 + 1):n]
  
  p.1 <- matrix(0, nrow = p1 + s*P1 + q1 + constant, ncol = 1)
  ph1<-matrix(ph.1,nrow=p1+constant,ncol=1)
  PH1<-matrix(PH.1,nrow=P1 ,ncol=1)
  qh1<-matrix(qh.1,nrow=q1,ncol=1)
  
  
  
  for (i in 1:(p1+constant)){
    p.1[i]<-ph1[i]
  }
  for (i in 1:P1){
    p.1[i*s+constant]<-PH1[i]
  }
  for (i in 1:P1){
    for (j in 1:p1){
      p.1[i*s+j+constant]<- -ph1[j+constant]*PH1[i]
    }
  }
  for (i in 1:q1){
    p.1[p1+s*P1+constant+i]<-qh1[i]
  }
  
  x.1 <- matrix(0, nrow = p1+s*P1+q1, ncol = (n - P11))
  x.11<-matrix(NA, nrow = p1, ncol = (n-P11))
  x.12<-matrix(NA, nrow = P1, ncol = (n-P11))
  x.13<-vector("list",P1)
  for (j in 1:P1){
    x.13[[j]]<-matrix(NA, nrow = p1, ncol = (n-P11))
  }
  x.14<-matrix(NA, nrow = q1, ncol = (n-P11))
  
  
  
  y.1 <- matrix(yt, ncol = 1)
  
  
  for (i in 1:p1){
    x.11[i,]<-ay[(P11 - lagp1[i] + 1):(n - lagp1[i])] 
  }
  x.1[1:p1,]<-x.11
  for (i in 1:P1){
    x.12[i,]<-ay[(P11 - lagP1[i]*s + 1):(n - lagP1[i]*s)]
  }
  x.1[seq(s,P1*s,s),]<-x.12
  for (i in 1:P1){
    for (j in 1:p1){
      x.13[[i]][j,]<-ay[(P11 - (lagp1[j]+s*lagP1[i]) + 1):(n -(lagp1[j]+s*lagP1[i]))]
    }
  }
  for (i in 1:P1){ 
    x.1[seq(i*s+1,i*s+p1,1),]<-x.13[[i]]
  }
  for (i in 1:q1) {
    x.14[i, ] <- thresVar[(P11 - lagq1[i] + 1):(n - lagq1[i])]
  }
  x.1[(p1+s*P1+1):(p1+s*P1+q1),]<-x.14
  if (constant == 1) {
    tx.1 <- cbind(1, t(x.1))
  }
  else {
    tx.1 <- t(x.1)
  }
  
  
  ln.li <-  -(((n-P11)*log(2*pi))/2)-((t(y.1 - tx.1 %*% p.1) %*% (y.1 - tx.1 %*% p.1))/(2 *sig.1)) - ((n/2) * log(sig.1)) 
  
  return(ln.li)
}





######################## cálculo de estadísticas resumen       
###############################################################  are.summaryx
#####  x es par.set del programa principal


are.summaryx=function (x, lagp1, lagP1,  lagq1,  constant) 
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
      rownames(temp) <- c(paste("phi", c(0, lagp1), sep = "."), paste("PHI", lagP1, sep = "."), paste("qhi", lagq1, sep = "."), "sigma^2 ")
    }
    if(constant==0) {
      rownames(temp) <- c(paste("phi", lagp1, sep = "."), paste("PHI", lagP1, sep = "."), paste("qhi", lagq1, sep = "."), "sigma^2 ")
    }
    
  }
  return(temp)
}


###################################################################
####################################



########################################        programa principal    Estimación Bayesiana, residuales   
##############################################       BAYESE.ARX



BAYESE.ARX=function(x, lagp1, lagP1, lagq1, Iteration, Burnin, constant, thresVar, s)
  
{
  
  refresh<-1000
  p1 <- length(lagp1)
  P1 <- length(lagP1)
  q1 <- length(lagq1)
  nx <- length(x)
  
  
  ########## condiciones iniciales #################
  
  phi.1=rep(0.05,p1+constant)
  PHI.1=rep(0.05,P1)
  qhi.1=rep(0.05,q1)
  sigma.1=0.20
  
  ############# hiperpar?metros ##############
  
  mu0ph1=matrix(0,nrow=p1+constant,ncol=1)
  v0ph1=diag(0.1,p1+constant)
  
  mu0PH1=matrix(0,nrow=P1,ncol=1)
  v0PH1=diag(0.1,P1)
  
  mu0qh1=matrix(0,nrow=q1,ncol=1)
  v0qh1=diag(0.1,q1)
  
  v0=3
  lambda0=var(x)/3
  
  
  
  ####################################################################
  
  par.set <- matrix(NA, nrow = Iteration, ncol = (length(c(phi.1, PHI.1, qhi.1, sigma.1))))
  loglik.1 <- loglik.2 <- DIC <-lnaprioris<-logvermarg<-NA
  
  for (igb in 1:Iteration) {
    
    phi.1 <- are.coeffxph(x, p1, P1, q1, sigma.1, mu0ph1, v0ph1, PHI.1, qhi.1, lagp1, lagP1, lagq1, constant, thresVar, s)
    
    PHI.1 <- are.coeffxPH(x, p1, P1, q1, sigma.1, mu0PH1, v0PH1, phi.1, qhi.1, lagp1, lagP1, lagq1, constant, thresVar, s) 
    
    qhi.1 <- are.coeffxqh(x, p1, P1, q1, sigma.1, mu0qh1, v0qh1, phi.1, PHI.1, lagp1, lagP1, lagq1, constant, thresVar, s)
    
    sigma.1 <- are.sigmax(x, p1, P1, q1, phi.1, PHI.1, qhi.1, v0, lambda0, lagp1, lagP1, lagq1, constant, thresVar, s)
    
    
    par.set[igb, ] <- c(phi.1, PHI.1, qhi.1, sigma.1)
    
    loglik.1[igb] <- are.likx(x, p1, P1, q1, phi.1, PHI.1, qhi.1,  sigma.1, lagp1, lagP1, lagq1, constant, thresVar, s)
    
    lnaprioris[igb]<- -0.5*((p1+constant)*log(2*pi)+(p1+constant)*log(det(solve(v0ph1)))+phi.1%*%v0ph1%*%t(phi.1))-0.5*(P1*log(2*pi)+P1*log(det(solve(v0PH1)))+PHI.1%*%v0PH1%*%t(PHI.1))-0.5*(q1*log(2*pi)+q1*log(det(solve(v0qh1)))+qhi.1%*%v0qh1%*%t(qhi.1))+(1.5*log(var(x)/2)-log(gamma(1.5))-2.5*log(sigma.1)-0.5*var(x)*(1/sigma.1))
    
    logvermarg[igb]<-loglik.1[igb]+lnaprioris[igb]
    
    
    
    ncol0 <- ncol(par.set)
    
    if (igb%%refresh == 0) 
    {
      cat("------------", "\n")
      cat("iteration = ", igb, "\n")
      cat("ph = ", round(phi.1, 4), "\n")
      cat("PH = ", round(PHI.1, 4), "\n")
      cat("qh = ", round(qhi.1, 4), "\n")
      cat("sigma^2  = ", round(sigma.1, 4), "\n")
      
      
    }
    
  }   ### fin del igb
  
  
  mcmc.stat <- are.summaryx(par.set[(Burnin + 1):Iteration, ], lagp1, lagP1, lagq1, constant)
  print(round(mcmc.stat, 4))
  
  
  
  loglik.2<-are.likx(x, p1, P1, q1, mcmc.stat[1:(p1+ constant), 1], mcmc.stat[(p1+constant+1):(p1+constant+P1), 1], mcmc.stat[(p1+constant+P1+1):(p1+constant+P1+q1), 1], mcmc.stat[(p1+constant+P1+q1+1), 1], lagp1, lagP1, lagq1, constant, thresVar, s )
  
  DIC<- (2*(-2*sum(loglik.1[(Burnin + 1):Iteration]))/length(loglik.1[(Burnin + 1):Iteration])) - (-2*loglik.2)
  cat(" DIC = ", DIC, "\n")
  
  #lnapriorisfijo<-NA
  #lnapriorisfijo<- -0.5*((p1+constant)*log(2*pi)+(p1+constant)*log(det(solve(v0ph1)))+t(mcmc.stat[1:(p1+ constant), 1])%*%v0ph1%*%(mcmc.stat[1:(p1 + constant), 1]))-0.5*(P1*log(2*pi)+P1*log(det(solve(v0PH1)))+t(mcmc.stat[(p1+constant+1):(p1+constant+P1), 1])%*%v0PH1%*%(mcmc.stat[(p1+constant+1):(p1+constant+P1), 1]))-0.5*(q1*log(2*pi)+q1*log(det(solve(v0qh1)))+t(mcmc.stat[(p1+constant+P1+1):(p1+constant+P1+q1), 1])%*%v0qh1%*%(mcmc.stat[(p1+constant+P1+1):(p1+constant+P1+q1), 1]))+(1.5*log(var(x)/2)-log(gamma(1.5))-2.5*log( mcmc.stat[(p1 + constant+P1+q1 + 1), 1])-0.5*var(x)*(1/ mcmc.stat[(p1+ constant+P1+q1 + 1), 1]))
  
  
  if (constant==1) 
  {       
    con.1 <-  mcmc.stat[1, 1]
    parp.1 <- mcmc.stat[2:(p1+ constant), 1]
    parP.1 <- mcmc.stat[(p1+constant+1):(p1+constant+P1), 1]
    parq.1 <- mcmc.stat[(p1+constant+P1+1):(p1+constant+P1+q1), 1]
    
    sig.1u <- mcmc.stat[p1+constant+P1+q1+1,1]
    
  }
  
  
  if (constant== 0) 
  {       
    con.1 <- 0
    parp.1 <- mcmc.stat[1:p1, 1]
    parP.1 <- mcmc.stat[(p1+1):(p1+P1), 1]
    parq.1 <- mcmc.stat[(p1+P1+1):(p1+P1+q1), 1]
    
    sig.1u <- mcmc.stat[p1+P1+q1+1,1]
    
    
  }
  
  
  
  maxd <- max(max(lagp1)+s*max(lagP1), max(lagq1))
  
  
  residual <-residual.est<- rep(0, (nx - maxd))
  residual1 <- rep(0, (nx - maxd))
  
  
  multipP1<-matrix(NA,nrow=(nx-maxd), ncol=p1*P1)
  
  
  for (t in (maxd + 1):nx) {
    
    
    
    for (i in 1:P1){
      for (j in 1:p1){
        multipP1[t-maxd, (i*j+(p1-j)*(i-1))]<-parP.1[i]*parp.1[j]*x[t-(lagp1[j]+s*lagP1[i])]
      }
    }
    
    residual[t - maxd] <- (x[t] - sum(con.1, parp.1[1:p1]*x[t - lagp1], parP.1[1:P1]*x[t - s*lagP1], -multipP1[t-maxd, ],  parq.1[1:q1]*thresVar[t - lagq1]))
    residual.est[t - maxd]<-residual[t - maxd]/sqrt(sig.1u)
    residual1[t - maxd] <- (x[t] - sum(con.1, parp.1[1:p1]*x[t - lagp1], parP.1[1:P1]*x[t - s*lagP1], - multipP1[t-maxd, ],  parq.1[1:q1]*thresVar[t - lagq1]))
    
  }
  
  res1<-sum(residual1^2)
  
  
  NAIC<-NA
  NAIC<- (nx*log(res1/nx)+2*(p1+constant+P1+q1))/nx
  cat("NAIC", NAIC,"\n")
  
  
  tar <- list(mcmc = par.set, posterior = par.set[(Burnin + 1):Iteration, ], coef.par = round(mcmc.stat, 4), residual = residual, residual.est=residual.est, DIC = DIC, NAIC=NAIC, logverosimil=loglik.1[(Burnin+1):Iteration], log.ver=logvermarg[(Burnin+1):Iteration])
  
  return(tar)
}

#######################       INICIO DEL  PROGRAMA  2 REGÍMENES   ######################################################## 





####################  Estimación de los coeficientes autorregresivos y exógenos      
########################    tar2e.coeffxph


tar2e.coeffxph=function(reg, ay, p, P, q, sig, lagd, thres, mu0ph, v0ph, PH, qh, lagp1, lagp2, lagP1, lagP2, lagq1, lagq2, constant, thresVar, s) 
{
  P11 <- max(max(lagp1)+s*max(lagP1), max(lagp2)+s*max(lagP2), max(lagq1), max(lagq2)) 
  n <- length(ay)
  lag.y <- thresVar[(P11 + 1 - lagd):(n - lagd)]
  yt <- ay[(P11 + 1):n]
  xxx.1<-vector("list",P)
  txxx.1<-vector("list",P)
  PH.1<-matrix(PH, nrow=P, ncol=1)
  qh.1<-matrix(qh, nrow=q, ncol=1)
  L<-matrix(NA, nrow=P, ncol=(n-P11))
  Q<-matrix(NA, nrow=q, ncol=(n-P11))
  xx.1 <- matrix(NA, nrow = p, ncol = (n-P11))
  for (j in 1:P){
    xxx.1[[j]]<-matrix(NA, nrow = p, ncol = (n-P11))
  }
  for (j in 1:P){
    txxx.1[[j]]<-matrix(NA, nrow =(n-P11) , ncol =p)
  }
  
  if (reg == 1) {
    for (i in 1:p){
      xx.1[i, ] <- ay[(P11-lagp1[i]+1):(n-lagp1[i])]
    }
    txx.1<-t(xx.1)
    for (j in 1:P){
      for (i in 1:p) {
        xxx.1[[j]][i,] <- ay[(P11-lagp1[i]-lagP1[j]*s+1):(n-lagp1[i]-lagP1[j]*s)]*PH[j]
      }
    }
    for (j in 1:P){
      
      txxx.1[[j]]<-t(xxx.1[[j]])
    }
    auxsuma<-matrix(0, nrow=nrow(txxx.1[[1]]) , ncol=p)
    for (k in 1:P){
      auxsuma<-auxsuma+txxx.1[[k]]
    }
    x.1t<-txx.1-auxsuma
    x.1<-t(x.1t)
    if (p==1){
      if (constant==1){
        tx <- cbind(1,t(t(x.1[,lag.y<=thres])))
      }
      else {
        tx<- t(t(x.1[,lag.y<=thres]))
      }
    }
    if (p>1){
      if (constant==1){
        
        tx <- cbind(1, t(x.1[,lag.y<=thres]))
      }
      else {
        tx<- t(x.1[,lag.y<=thres])
      }
    }
    for (i in 1:P){
      L[i,]<-ay[(P11-lagP1[i]*s+1):(n-lagP1[i]*s)]
    }
    for (i in 1:q){
      Q[i,]<-thresVar[(P11-lagq1[i]+1):(n-lagq1[i])]
    }
    Ytt<-yt-(t(L)%*%PH.1+t(Q)%*%qh.1)
    Yt<-matrix(Ytt[lag.y<=thres], ncol=1)
    sigma<-(t(tx)%*%tx)/sig + v0ph
    mu<-solve(sigma,(t(tx)%*%Yt)/sig + v0ph %*% mu0ph)
    ph<-rmvnorm(1,mu,solve(sigma),method = "chol")
  }
  
  else {
    for (i in 1:p){
      xx.1[i, ] <- ay[(P11-lagp2[i]+1):(n-lagp2[i])]
    }
    txx.1<-t(xx.1)    
    for (j in 1:P){
      for (i in 1:p) {
        xxx.1[[j]][i,] <- ay[(P11-lagp2[i]-lagP2[j]*s+1):(n-lagp2[i]-lagP2[j]*s)]*PH[j]
      }
    }
    for (j in 1:P){
      txxx.1[[j]]<-t(xxx.1[[j]])
    }
    auxsuma<-matrix(0, nrow=nrow(txxx.1[[1]]) , ncol=p)
    for (k in 1:P){
      auxsuma<-auxsuma+txxx.1[[k]]
    }
    x.1t<-txx.1-auxsuma
    x.1<-t(x.1t)
    if (p==1){
      if (constant==1){
        tx <- cbind(1,t(t(x.1[,lag.y>thres])))
      }
      else {
        tx<- t(t(x.1[,lag.y>thres]))
      }
    }
    if (p>1){
      if (constant==1){
        
        tx <- cbind(1, t(x.1[,lag.y>thres]))
      }
      else {
        tx<- t(x.1[,lag.y>thres])
      }
    }
    
    for (i in 1:P){
      L[i,]<-ay[(P11-lagP2[i]*s+1):(n-lagP2[i]*s)]
    }
    for (i in 1:q){
      Q[i,]<-thresVar[(P11-lagq2[i]+1):(n-lagq2[i])]
    }
    
    
    Ytt<-yt-(t(L)%*%PH.1+t(Q)%*%qh.1)
    Yt<-matrix(Ytt[lag.y>thres], ncol=1)
    sigma<-(t(tx)%*%tx)/sig + v0ph
    mu<-solve(sigma,(t(tx)%*%Yt)/sig + v0ph %*% mu0ph)
    ph<-rmvnorm(1,mu,solve(sigma),method = "chol")
  }
  return(ph)
}

#################################################################
#################################################



####################   Estimación de los coeficientes autorregresivos y exógenos       
########################    tar2e.coeffxPH



tar2e.coeffxPH=function(reg, ay, p, P, q, sig, lagd, thres, mu0PH, v0PH, ph, qh, lagp1, lagp2, lagP1, lagP2, lagq1, lagq2, constant, thresVar, s) 
{
  P11 <- max(max(lagp1)+s*max(lagP1), max(lagp2)+s*max(lagP2), max(lagq1), max(lagq2)) 
  n <- length(ay)
  lag.y <- thresVar[(P11 + 1 - lagd):(n - lagd)]
  yt <- ay[(P11 + 1):n]
  xxx.1<-vector("list",p)
  txxx.1<-vector("list",p)
  ph.1<-matrix(ph, nrow=p+constant, ncol=1)
  qh.1<-matrix(qh, nrow=q, ncol=1)
  L<-matrix(NA, nrow=p, ncol=(n-P11))
  Q<-matrix(NA, nrow=q, ncol=(n-P11))
  xx.1 <- matrix(NA, nrow = P, ncol = (n-P11))
  for (j in 1:p){
    xxx.1[[j]]<-matrix(NA, nrow = P, ncol = (n-P11))
  }
  for (j in 1:p){
    txxx.1[[j]]<-matrix(NA, nrow =(n-P11), ncol =P)
  }
  
  if (reg == 1) {
    for (i in 1:P){
      xx.1[i, ] <- ay[(P11-lagP1[i]*s+1):(n-lagP1[i]*s)]
    }
    txx.1<-t(xx.1)
    for (j in 1:p){
      for (i in 1:P) {
        xxx.1[[j]][i,] <- ay[(P11-lagP1[i]*s-lagp1[j]+1):(n-lagP1[i]*s-lagp1[j])]*ph[j+constant]
      }
    }
    for (j in 1:p){
      txxx.1[[j]]<-t(xxx.1[[j]])
    }
    auxsuma<-matrix(0, nrow=nrow(txxx.1[[1]]) , ncol=P)
    for (k in 1:p){
      auxsuma<-auxsuma+txxx.1[[k]]
    }
    x.1t<-txx.1-auxsuma
    x.1<-t(x.1t)
    
    if (P==1){
      tx <- t(t(x.1[,lag.y<=thres]))
    }
    
    if (P>1){
      tx <- t(x.1[,lag.y<=thres])
    }
    
    for (i in 1:p){
      L[i,]<-ay[(P11-lagp1[i]+1):(n-lagp1[i])]
    }
    if (constant==1){
      L<-cbind(1, t(L))
    }
    if (constant==0) {
      L<-t(L)
    }
    for (i in 1:q){
      Q[i,]<-thresVar[(P11-lagq1[i]+1):(n-lagq1[i])]
    }
    Ytt<-yt-(L%*%ph.1+t(Q)%*%qh.1)
    Yt<-matrix(Ytt[lag.y<=thres], ncol=1)
    sigma<-(t(tx)%*%tx)/sig + v0PH
    mu<-solve(sigma,(t(tx)%*%Yt)/sig + v0PH %*% mu0PH)
    PH<-rmvnorm(1,mu,solve(sigma),method = "chol")
  }
  
  else {
    for (i in 1:P){
      xx.1[i, ] <- ay[(P11-lagP2[i]*s+1):(n-lagP2[i]*s)]
    }
    
    txx.1<-t(xx.1)
    
    
    for (j in 1:p){
      for (i in 1:P) {
        xxx.1[[j]][i,] <- ay[(P11-lagP2[i]*s-lagp2[j]+1):(n-lagP2[i]*s-lagp2[j])]*ph[j+constant]
      }
    }
    
    
    for (j in 1:p){
      txxx.1[[j]]<-t(xxx.1[[j]])
    }
    
    auxsuma<-matrix(0, nrow=nrow(txxx.1[[1]]) , ncol=P)
    for (k in 1:p){
      auxsuma<-auxsuma+txxx.1[[k]]
    }
    x.1t<-txx.1-auxsuma
    x.1<-t(x.1t)
    
    if (P==1){
      tx <- t(t(x.1[,lag.y>thres]))
    }
    
    if (P>1){
      tx <- t(x.1[,lag.y>thres])
    }
    
    for (i in 1:p){
      L[i,]<-ay[(P11-lagp2[i]+1):(n-lagp2[i])]
    }
    if (constant==1){
      L<-cbind(1, t(L))
    }
    if (constant==0) {
      L<-t(L)
    }
    
    
    for (i in 1:q){
      Q[i,]<-thresVar[(P11-lagq2[i]+1):(n-lagq2[i])]
    }
    
    Ytt<-yt-(L%*%ph.1+t(Q)%*%qh.1)
    Yt<-matrix(Ytt[lag.y>thres], ncol=1)
    sigma<-(t(tx)%*%tx)/sig + v0PH
    mu<-solve(sigma,(t(tx)%*%Yt)/sig + v0PH %*% mu0PH)
    PH<-rmvnorm(1,mu,solve(sigma),method = "chol")
    
    
  }
  return(PH)
}

#################################################################
#################################################




####################   Estimación de los coeficientes autorregresivos y exógenos       
########################    tar2e.coeffxqh


tar2e.coeffxqh=function(reg, ay, p, P, q, sig, lagd, thres, mu0qh, v0qh, ph, PH, lagp1, lagp2, lagP1, lagP2, lagq1, lagq2, constant, thresVar, s) 
{
  P11 <- max(max(lagp1)+s*max(lagP1), max(lagp2)+s*max(lagP2), max(lagq1), max(lagq2)) 
  n <- length(ay)
  lag.y <- thresVar[(P11 + 1 - lagd):(n - lagd)]
  yt <- ay[(P11 + 1):n]
  ph.1<-matrix(ph, nrow=p+constant, ncol=1)
  PH.1<-matrix(PH, nrow=P, ncol=1)
  A<-matrix(NA, nrow=P*(s-1), ncol=(n-P11))
  L<-matrix(NA, nrow=p, ncol=(n-P11))
  Q<-matrix(NA, nrow=P, ncol=(n-P11))
  x.1 <- matrix(NA, nrow = q, ncol = (n-P11))
  yy=vector("list", P)
  for (j in 1:P){
    yy[[j]]<-matrix(NA, nrow=(s-1), ncol=(n-P11))
  }
  coefaux<- matrix(NA, nrow = P*(s-1), ncol =1)
  xx=vector("list", P)
  for (j in 1:P){
    xx[[j]]<-matrix(NA, nrow=(s-1), ncol=1)
  }
  
  
  for (i in 1:P){
    
    xx[[i]][1:(s-p-1),]<-rep(0,(s-p-1))
    
    xx[[i]][(s-p):(s-1), ]<- -ph[(1+constant):(p+constant)]*PH[i]
    
  }
  
  for (j in 1:P){
    coefaux[((j-1)*(s-p-1)+(j-1)*p+1):(j*(s-p-1)+(j-1)*p),]<-xx[[j]][1:(s-p-1),] 
    coefaux[(j*(s-p-1)+(j-1)*p+1):(j*(s-p-1)+j*p),]<- xx[[j]][(s-p):(s-1), ]
  }
  
  
  if (reg == 1) {
    
    for (i in 1:q){
      x.1[i, ] <- thresVar[(P11-lagq1[i]+1):(n-lagq1[i])]
    }
    
    if (q==1){
      tx<- t(t(x.1[ ,lag.y<=thres]))
    }
    if (q>1){
      tx<- t(x.1[ ,lag.y<=thres])
    }
    
    for (i in 1:p){
      L[i,]<-ay[(P11-lagp1[i]+1):(n-lagp1[i])]
    }
    if (constant==1){
      L<-cbind(1, t(L))
    }
    
    if (constant==0) {
      L<-t(L)
    }
    
    for (i in 1:P){
      Q[i,]<-ay[(P11-lagP1[i]*s+1):(n-lagP1[i]*s)]
    }
    
    for (j in 1:P){
      for (i in 1:(s-p-1)){
        yy[[j]][i,]<-ay[(P11-((j-1)*s+p+i)+1):(n-((j-1)*s+p+i))]
      }
      for (k in (s-p-1+1):(s-1)){
        yy[[j]][k, ]<-ay[(P11-(j*s+ k-(s-p-1))+1):(n-(j*s+k-(s-p-1)))]
      }
    }
    for (j in 1:P){
      A[((j-1)*(s-p-1)+(j-1)*p+1):(j*(s-p-1)+(j-1)*p),]<- yy[[j]][1:(s-p-1),]
      A[(j*(s-p-1)+(j-1)*p+1):(j*(s-p-1)+j*p),]<- yy[[j]][(s-p-1+1):(s-1),]
    }
    Ytt<-yt-(t(A)%*%coefaux+L%*%ph.1+t(Q)%*%PH.1)
    Yt<-matrix(Ytt[lag.y<=thres], ncol=1)
    sigma<-(t(tx)%*%tx)/sig + v0qh
    mu<-solve(sigma,(t(tx)%*%Yt)/sig + v0qh %*% mu0qh)
    qh<-rmvnorm(1,mu,solve(sigma),method = "chol")
  }
  else {
    
    for (i in 1:q){
      x.1[i, ] <- thresVar[(P11-lagq2[i]+1):(n-lagq2[i])]
    }
    
    if (q==1){
      tx<- t(t(x.1[ ,lag.y>thres]))
    }
    if (q>1){
      tx<- t(x.1[ ,lag.y>thres])
    }
    for (i in 1:p){
      L[i,]<-ay[(P11-lagp2[i]+1):(n-lagp2[i])]
    }
    
    if (constant==1){
      L<-cbind(1, t(L))
    }
    if (constant==0) {
      L<-t(L)
    }
    
    for (i in 1:P){
      Q[i,]<-ay[(P11-lagP2[i]*s+1):(n-lagP2[i]*s)]
    }
    
    for (j in 1:P){
      for (i in 1:(s-p-1)){
        yy[[j]][i,]<-ay[(P11-((j-1)*s+p+i)+1):(n-((j-1)*s+p+i))]
      }
      for (k in (s-p-1+1):(s-1)){
        yy[[j]][k, ]<-ay[(P11-(j*s+ k-(s-p-1))+1):(n-(j*s+k-(s-p-1)))]
      }
    }
    for (j in 1:P){
      A[((j-1)*(s-p-1)+(j-1)*p+1):(j*(s-p-1)+(j-1)*p),]<- yy[[j]][1:(s-p-1),]
      A[(j*(s-p-1)+(j-1)*p+1):(j*(s-p-1)+j*p),]<- yy[[j]][(s-p-1+1):(s-1),]
    }
    
    Ytt<-yt-(t(A)%*%coefaux+L%*%ph.1+t(Q)%*%PH.1)
    Yt<-matrix(Ytt[lag.y>thres], ncol=1)
    sigma<-(t(tx)%*%tx)/sig + v0qh
    mu<-solve(sigma,(t(tx)%*%Yt)/sig + v0qh %*% mu0qh)
    qh<-rmvnorm(1,mu,solve(sigma),method = "chol")
  }
  return(qh)
}

#################################################################
#################################################


############### Extraer la varianza de la distribución de los errores      
##################  tar2e.sigmax

tar2e.sigmax=function(reg, ay, thres, lagd, p, P, q, ph, PH, qh, v, lambda, lagp1, lagp2, lagP1, lagP2, lagq1, lagq2, constant, thresVar, s)
{
  P11 <- max(max(lagp1)+s*max(lagP1), max(lagp2)+s*max(lagP2), max(lagq1), max(lagq2)) 
  n <- length(ay)
  lag.y <- thresVar[(P11 + 1 - lagd):(n - lagd)]
  yt <- ay[(P11 + 1):n]
  x.1 <- matrix(0, nrow = p+s*P+q, ncol = (n - P11))
  x.11<-matrix(NA, nrow = p, ncol = (n-P11))
  x.12<-matrix(NA, nrow = P, ncol = (n-P11))
  x.13<-vector("list",P)
  for (j in 1:P){
    x.13[[j]]<-matrix(NA, nrow = p, ncol = (n-P11))
  }
  x.14<-matrix(NA, nrow = q, ncol = (n-P11))
  
  p.1<-matrix(0,nrow=p+s*P+q+constant,ncol=1)
  ph<-matrix(ph,nrow=p+constant,ncol=1)
  PH<-matrix(PH,nrow=P,ncol=1)
  qh<-matrix(qh, nrow=q,ncol=1)
  
  
  for (i in 1:(p+constant)){
    p.1[i]<-ph[i]
  }
  for (i in 1:P){
    p.1[i*s+constant]<-PH[i]
  }
  for (i in 1:P){
    for (j in 1:p){
      p.1[i*s+j+constant]<- -ph[j+constant]*PH[i]
    }
  }
  for (i in 1:q){
    p.1[p+s*P+constant+i]<-qh[i]
  }
  
  if (reg == 1) {
    m <- sum(lag.y <= thres)
    y<- matrix(yt[lag.y <= thres], ncol = 1)
    for (i in 1:p){
      x.11[i,]<-ay[(P11 - lagp1[i] + 1):(n - lagp1[i])] 
    }
    x.1[1:p,]<-x.11
    for (i in 1:P){
      x.12[i,]<-ay[(P11 - lagP1[i]*s + 1):(n - lagP1[i]*s)]
    }
    x.1[seq(s,P*s,s),]<-x.12
    
    for (i in 1:P){
      for (j in 1:p){
        x.13[[i]][j,]<-ay[(P11 - (lagp1[j]+s*lagP1[i]) + 1):(n -(lagp1[j]+s*lagP1[i]))]
      }
    }
    for (i in 1:P){ 
      x.1[seq(i*s+1,i*s+p,1),]<-x.13[[i]]
    }
    for (i in 1:q) {
      x.14[i, ] <- thresVar[(P11 - lagq1[i] + 1):(n - lagq1[i])]
    }
    x.1[(p+s*P+1):(p+s*P+q),]<-x.14
    
    if (constant==1){
      tx <- cbind(1, t(x.1[,lag.y <= thres]))
    }
    if (constant==0) {
      tx <- t(x.1[,lag.y <= thres])
    }
    
    s2 <- (t(y-tx%*%p.1)%*%(y-tx%*%p.1))/m
    
  }
  
  else 
  {
    m <- sum(lag.y>thres)
    y<- matrix(yt[lag.y>thres], ncol = 1)
    for (i in 1:p){
      x.11[i,]<-ay[(P11 - lagp2[i] + 1):(n - lagp2[i])] 
    }
    x.1[1:p,]<-x.11
    for (i in 1:P){
      x.12[i,]<-ay[(P11 - lagP2[i]*s + 1):(n - lagP2[i]*s)]
    }
    x.1[seq(s,P*s,s),]<-x.12
    
    for (i in 1:P){
      for (j in 1:p){
        x.13[[i]][j,]<-ay[(P11 - (lagp2[j]+s*lagP2[i]) + 1):(n -(lagp2[j]+s*lagP2[i]))]
      }
    }
    for (i in 1:P){ 
      x.1[seq(i*s+1,i*s+p,1),]<-x.13[[i]]
    }
    for (i in 1:q) {
      x.14[i, ] <- thresVar[(P11 - lagq2[i] + 1):(n - lagq2[i])]
    }
    x.1[(p+s*P+1):(p+s*P+q),]<-x.14
    
    if (constant==1){
      tx <- cbind(1, t(x.1[,lag.y>thres]))
    }
    if (constant==0) {
      tx <- t(x.1[,lag.y>thres])
    }
    
    s2 <- (t(y-tx%*%p.1)%*%(y-tx%*%p.1))/m
    
  }
  
  shape <- (v + m)/2
  rate <- (v*lambda + m*s2)/2
  sigma <- 1/rgamma(1, shape, rate)
  return(sigma)
}

#############################################################################
##########################################


###################### calcular la función log.verosimil       
############################ tar2e.likx


tar2e.likx=function(ay, p1, p2, P1, P2, q1, q2, ph.1, PH.1, qh.1, ph.2, PH.2, qh.2, sig.1, sig.2, lagd, thres, lagp1, lagp2, lagP1, lagP2, lagq1, lagq2, constant, thresVar, s) 
  
{
  P11 <- max(max(lagp1)+s*max(lagP1), max(lagp2)+s*max(lagP2), max(lagq1), max(lagq2)) 
  n <- length(ay)
  lag.y <- thresVar[(P11 + 1 - lagd):(n - lagd)]
  yt <- ay[(P11 + 1):n]
  
  p.1 <- matrix(0, nrow = p1 + s*P1 + q1 + constant, ncol = 1)
  ph1<-matrix(ph.1,nrow=p1+constant,ncol=1)
  PH1<-matrix(PH.1,nrow=P1 ,ncol=1)
  qh1<-matrix(qh.1,nrow=q1,ncol=1)
  
  p.2 <- matrix(0, nrow = p2 + s*P2 + q2 + constant, ncol = 1)
  ph2<-matrix(ph.2,nrow=p2+constant,ncol=1)
  PH2<-matrix(PH.2,nrow=P2,ncol=1)
  qh2<-matrix(qh.2,nrow=q2,ncol=1)
  
  
  for (i in 1:(p1+constant)){
    p.1[i]<-ph1[i]
  }
  for (i in 1:P1){
    p.1[i*s+constant]<-PH1[i]
  }
  for (i in 1:P1){
    for (j in 1:p1){
      p.1[i*s+j+constant]<- -ph1[j+constant]*PH1[i]
    }
  }
  for (i in 1:q1){
    p.1[p1+s*P1+constant+i]<-qh1[i]
  }
  
  
  for (i in 1:(p2+constant)){
    p.2[i]<-ph2[i]
  }
  for (i in 1:P2){
    p.2[i*s+constant]<-PH2[i]
  }
  for (i in 1:P2){
    for (j in 1:p2){
      p.2[i*s+j+constant]<- -ph2[j+constant]*PH2[i]
    }
  }
  for (i in 1:q2){
    p.2[p2+s*P2+constant+i]<-qh2[i]
  }
  x.1 <- matrix(0, nrow = p1+s*P1+q1, ncol = (n - P11))
  x.11<-matrix(NA, nrow = p1, ncol = (n-P11))
  x.12<-matrix(NA, nrow = P1, ncol = (n-P11))
  x.13<-vector("list",P1)
  for (j in 1:P1){
    x.13[[j]]<-matrix(NA, nrow = p1, ncol = (n-P11))
  }
  x.14<-matrix(NA, nrow = q1, ncol = (n-P11))
  x.2 <- matrix(0, nrow = p2+s*P2+q2, ncol = (n - P11))
  x.21<-matrix(NA, nrow = p2, ncol = (n-P11))
  x.22<-matrix(NA, nrow = P2, ncol = (n-P11))
  x.23<-vector("list",P2)
  for (j in 1:P2){
    x.23[[j]]<-matrix(NA, nrow = p2, ncol = (n-P11))
  }
  x.24<-matrix(NA, nrow = q2, ncol = (n-P11))
  
  n1 <- sum(lag.y <= thres)
  n2 <- sum(lag.y > thres)
  y.1 <- matrix(yt[lag.y <= thres], ncol = 1)
  y.2 <- matrix(yt[lag.y > thres], ncol = 1)
  
  for (i in 1:p1){
    x.11[i,]<-ay[(P11 - lagp1[i] + 1):(n - lagp1[i])] 
  }
  x.1[1:p1,]<-x.11
  for (i in 1:P1){
    x.12[i,]<-ay[(P11 - lagP1[i]*s + 1):(n - lagP1[i]*s)]
  }
  x.1[seq(s,P1*s,s),]<-x.12
  for (i in 1:P1){
    for (j in 1:p1){
      x.13[[i]][j,]<-ay[(P11 - (lagp1[j]+s*lagP1[i]) + 1):(n -(lagp1[j]+s*lagP1[i]))]
    }
  }
  for (i in 1:P1){ 
    x.1[seq(i*s+1,i*s+p1,1),]<-x.13[[i]]
  }
  for (i in 1:q1) {
    x.14[i, ] <- thresVar[(P11 - lagq1[i] + 1):(n - lagq1[i])]
  }
  x.1[(p1+s*P1+1):(p1+s*P1+q1),]<-x.14
  
  if (constant==1){
    
    tx.1 <- cbind(1, t(x.1[ ,lag.y<=thres]))
  }
  if (constant==0){
    
    tx.1 <- t(x.1[ ,lag.y<=thres])
  }
  
  
  
  for (i in 1:p2){
    x.21[i,]<-ay[(P11 - lagp2[i] + 1):(n - lagp2[i])] 
  }
  x.2[1:p2,]<-x.21
  for (i in 1:P2){
    x.22[i,]<-ay[(P11 - lagP2[i]*s + 1):(n - lagP2[i]*s)]
  }
  x.2[seq(s,P2*s,s),]<-x.22
  for (i in 1:P2){
    for (j in 1:p2){
      x.23[[i]][j,]<-ay[(P11 - (lagp2[j]+s*lagP2[i]) + 1):(n -(lagp2[j]+s*lagP2[i]))]
    }
  }
  for (i in 1:P2){ 
    x.2[seq(i*s+1,i*s+p2,1),]<-x.23[[i]]
  }
  for (i in 1:q2) {
    x.24[i, ] <- thresVar[(P11 - lagq2[i] + 1):(n - lagq2[i])]
  }
  x.2[(p2+s*P2+1):(p2+s*P2+q2),]<-x.24
  
  if (constant==1){
    
    tx.2 <- cbind(1, t(x.2[ ,lag.y>thres]))
  }
  if (constant==0){
    
    tx.2 <- t(x.2[ ,lag.y>thres])
  }
  
  
  ln.li <-  -(((n-P11)*log(2*pi))/2) -((t(y.1 - tx.1 %*% p.1) %*% (y.1 - tx.1 %*% p.1))/(2 *sig.1)) - ((t(y.2 - tx.2 %*% p.2) %*% (y.2 - tx.2 %*% p.2))/(2 * sig.2)) - ((n1/2) * log(sig.1)) - ((n2/2) * log(sig.2))
  
  return(ln.li)
}


##################################################################################
##############################################################



###################### Extrae el valor umbral        
#############################   tar2e.thresxG      Metropolis-Hasting, con densidad instrumental GAUSSIANA 


tar2e.thresxG=function (ay, p1, p2, P1, P2,  q1, q2, ph.1, ph.2, PH.1, PH.2, qh.1, qh.2, sig.1, sig.2, lagd, thres, step.r, h, bound, lagp1, lagp2, lagP1, lagP2, lagq1, lagq2, constant,  thresVar, s) 
{
  P11 <- max(max(lagp1)+s*max(lagP1), max(lagp2)+s*max(lagP2), max(lagq1), max(lagq2)) 
  n <- length(ay)
  lag.y <- thresVar[(P11 + 1 - lagd):(n - lagd)]
  
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
  
  old.lik <- tar2e.likx(ay, p1, p2, P1, P2, q1, q2, ph.1, PH.1, qh.1, ph.2, PH.2, qh.2,  sig.1, sig.2, lagd, thres, lagp1, lagp2, lagP1, lagP2, lagq1, lagq2, constant, thresVar, s)
  new.lik <- tar2e.likx(ay, p1, p2, P1, P2, q1, q2, ph.1, PH.1, qh.1, ph.2, PH.2, qh.2,  sig.1, sig.2, lagd, new.r, lagp1, lagp2, lagP1, lagP2, lagq1, lagq2, constant, thresVar, s)
  
  
  if ((new.lik - old.lik) > log(runif(1))) {
    r.count = 1
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





#############  Identificación del rezago  d       
#####################    tar2e.lagdx


tar2e.lagdx=function(ay, p1, p2, P1, P2, q1, q2, ph.1, ph.2, PH.1, PH.2, qh.1, qh.2, sig.1, sig.2, thres, lagp1, lagp2, lagP1, lagP2, lagq1, lagq2, d0, constant, thresVar, s) 
{
  loglik <- lik <- NULL
  
  for (i in 1:(d0+1)) {
    
    loglik[i] <- tar2e.likx(ay, p1, p2, P1, P2, q1, q2, ph.1, PH.1, qh.1, ph.2, PH.2, qh.2, sig.1, sig.2, (i-1), thres, lagp1, lagp2, lagP1, lagP2, lagq1, lagq2, constant, thresVar, s)
    
  }
  lik <- exp(loglik - max(loglik))
  lagd <- (sum((cumsum(lik)/sum(lik)) < runif(1, min = 0, max = 1)))
  return(lagd)
}


###################################################################################
#####################################################


######################## cálculo de estadísticas resumen       
###############################################################  tar2e.summaryx
#####  x es par.set del programa principal


tar2e.summaryx=function (x, lagp1, lagp2, lagP1, lagP2,  lagq1, lagq2, constant) 
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
    
    if (constant==1){
      
      rownames(temp) <- c(paste("phi1", c(0,lagp1), sep = "."), paste("PHI1", lagP1, sep = "."), paste("qhi1", lagq1, sep = "."),paste("phi2", c(0,lagp2), sep = "."),paste("PHI2", lagP2, sep = "."), paste("qhi2", lagq2, sep = "."), "sigma^2 1", "sigma^2 2", "r")
    }
    if (constant==0){
      
      rownames(temp) <- c(paste("phi1", lagp1, sep = "."), paste("PHI1", lagP1, sep = "."), paste("qhi1", lagq1, sep = "."),paste("phi2", lagp2, sep = "."),paste("PHI2", lagP2, sep = "."), paste("qhi2", lagq2, sep = "."), "sigma^2 1", "sigma^2 2", "r")
    }
    
  }
  return(temp)
}


###################################################################
####################################



########################################        programa principal    Estimación Bayesiana, residuales   
##############################################       BAYES2E.TARX


BAYES2E.TARX=function(x, lagp1, lagp2, lagP1, lagP2,  lagq1, lagq2, Iteration, Burnin, step.thv, h, constant, thresVar, s, d0)
  
{
  refresh<-1000
  
  p1 <- length(lagp1)
  p2 <- length(lagp2)
  P1 <- length(lagP1)
  P2 <- length(lagP2)
  q1 <- length(lagq1)
  q2 <- length(lagq2)
  nx <- length(x)
  
  
  ########## condiciones iniciales #################
  
  
  phi.1=rep(0.05,p1+constant)
  phi.2=rep(0.05,p2+constant)
  PHI.1=rep(0.05,P1)
  PHI.2=rep(0.05,P2)
  qhi.1=rep(0.05,q1)
  qhi.2=rep(0.05,q2)
  sigma.1=0.20
  sigma.2=0.20
  lagd=3
  thres=median(thresVar)
  
  accept.r=0
  sum.r=0
  
  ############# hiperparámetros ##############
  
  
  mu0ph1=matrix(0,nrow=p1+constant,ncol=1)
  v0ph1=diag(0.1,p1+constant)
  mu0ph2=matrix(0,nrow=p2+constant,ncol=1)
  v0ph2=diag(0.1,p2+constant)
  mu0PH1=matrix(0,nrow=P1,ncol=1)
  v0PH1=diag(0.1,P1)
  mu0PH2=matrix(0,nrow=P2,ncol=1)
  v0PH2=diag(0.1,P2)
  mu0qh1=matrix(0,nrow=q1,ncol=1)
  v0qh1=diag(0.1,q1)
  mu0qh2=matrix(0,nrow=q2,ncol=1)
  v0qh2=diag(0.1,q2)
  v0=3
  lambda0=var(x)/3
  bound.thv=c(min(thresVar),max(thresVar))
  
  
  ####################################################################
  
  par.set <- matrix(NA, nrow = Iteration, ncol =(length(c(phi.1, PHI.1, qhi.1, phi.2, PHI.2, qhi.2, sigma.1, sigma.2, thres, lagd))))
  loglik.1 <- loglik.2 <- DIC <-lnaprioris<-logvermarg<-NA
  
  for (igb in 1:Iteration) {
    
    
    phi.1 <- tar2e.coeffxph(1, x, p1, P1, q1, sigma.1, lagd, thres, mu0ph1, v0ph1, PHI.1, qhi.1, lagp1, lagp2, lagP1, lagP2, lagq1, lagq2, constant, thresVar, s)
    phi.2 <- tar2e.coeffxph(2, x, p2, P2, q2, sigma.2, lagd, thres, mu0ph2, v0ph2, PHI.2, qhi.2, lagp1, lagp2, lagP1, lagP2, lagq1, lagq2,constant, thresVar, s)
    PHI.1 <- tar2e.coeffxPH(1, x, p1, P1, q1, sigma.1, lagd, thres, mu0PH1, v0PH1, phi.1, qhi.1, lagp1, lagp2, lagP1, lagP2, lagq1, lagq2,constant, thresVar, s) 
    PHI.2 <- tar2e.coeffxPH(2, x, p2, P2, q2, sigma.2, lagd, thres, mu0PH2, v0PH2, phi.2, qhi.2, lagp1, lagp2, lagP1, lagP2, lagq1, lagq2,constant, thresVar, s)
    qhi.1 <- tar2e.coeffxqh(1, x, p1, P1, q1, sigma.1, lagd, thres, mu0qh1, v0qh1, phi.1, PHI.1, lagp1, lagp2, lagP1, lagP2, lagq1, lagq2,constant, thresVar, s)
    qhi.2 <- tar2e.coeffxqh(2, x, p2, P2, q2, sigma.2, lagd, thres, mu0qh2, v0qh2, phi.2, PHI.2, lagp1, lagp2, lagP1, lagP2, lagq1, lagq2,constant, thresVar, s) 
    sigma.1 <- tar2e.sigmax(1, x, thres, lagd, p1, P1, q1, phi.1, PHI.1, qhi.1, v0, lambda0, lagp1, lagp2, lagP1, lagP2, lagq1, lagq2,constant, thresVar, s)
    sigma.2 <- tar2e.sigmax(2, x, thres, lagd, p2, P2, q2, phi.2, PHI.2, qhi.2, v0, lambda0, lagp1, lagp2, lagP1, lagP2, lagq1, lagq2,constant, thresVar, s)
    lagd <-tar2e.lagdx(x, p1, p2, P1, P2, q1, q2, phi.1, phi.2, PHI.1, PHI.2, qhi.1, qhi.2, sigma.1, sigma.2, thres, lagp1, lagp2, lagP1, lagP2, lagq1, lagq2, d0, constant, thresVar, s) 
    thresholdt<-tar2e.thresxG(x, p1, p2, P1, P2,  q1, q2, phi.1, phi.2, PHI.1, PHI.2, qhi.1, qhi.2, sigma.1, sigma.2, lagd, thres, step.thv, h, bound.thv, lagp1, lagp2, lagP1, lagP2, lagq1, lagq2, constant, thresVar, s)
    
    
    sum.r <- sum.r + thresholdt$r.count
    thres <- thresholdt$new.r
    
    par.set[igb, ] <- c(phi.1, PHI.1, qhi.1, phi.2, PHI.2, qhi.2, sigma.1, sigma.2, thres, lagd)
    
    loglik.1[igb] <- tar2e.likx(x, p1, p2, P1, P2, q1, q2, phi.1, PHI.1, qhi.1, phi.2, PHI.2, qhi.2,  sigma.1, sigma.2, lagd, thres, lagp1, lagp2, lagP1, lagP2, lagq1, lagq2, constant, thresVar, s)
    
    lnaprioris[igb]<- -0.5*((p1+constant)*log(2*pi)+(p1+constant)*log(det(solve(v0ph1)))+phi.1%*%v0ph1%*%t(phi.1))-0.5*((p2+constant)*log(2*pi)+(p2+constant)*log(det(solve(v0ph2)))+phi.2%*%v0ph2%*%t(phi.2))-0.5*(P1*log(2*pi)+P1*log(det(solve(v0PH1)))+PHI.1%*%v0PH1%*%t(PHI.1))-0.5*(P2*log(2*pi)+P2*log(det(solve(v0PH2)))+PHI.2%*%v0PH2%*%t(PHI.2))-0.5*(q1*log(2*pi)+q1*log(det(solve(v0qh1)))+qhi.1%*%v0qh1%*%t(qhi.1))-0.5*(q2*log(2*pi)+q2*log(det(solve(v0qh2)))+qhi.2%*%v0qh2%*%t(qhi.2))+(1.5*log(var(x)/2)-log(gamma(1.5))-2.5*log(sigma.1)-0.5*var(x)*(1/sigma.1))+(1.5*log(var(x)/2)-log(gamma(1.5))-2.5*log(sigma.2)-0.5*var(x)*(1/sigma.2))+log(1/(bound.thv[2]-bound.thv[1]))+log(1/(d0+1))
    
    logvermarg[igb]<-loglik.1[igb]+lnaprioris[igb]
    
    
    ncol0 <- ncol(par.set)
    
    if (igb%%refresh == 0) 
    {
      cat("iteration = ", igb, "\n")
      
      cat("regime 1 = ", round(phi.1, 4), "\n")
      cat("regime 1 = ", round(PHI.1, 4), "\n")
      cat("regime 1 = ", round(qhi.1, 4), "\n")
      
      cat("regime 2 = ", round(phi.2, 4), "\n")
      cat("regime 2 = ", round(PHI.2, 4), "\n")
      cat("regime 2 = ", round(qhi.2, 4), "\n")
      
      cat("sigma^2 1  = ", round(sigma.1, 4), "\n")
      cat("sigma^2 2  = ", round(sigma.2, 4), "\n")
      
      cat("r        = ", round(thres, 4), "\n")
      
      accept.r <- (sum.r/igb)*100
      cat("Tasa de aceptación de r = ", round(accept.r, 4), "%", "\n")
      lag.freq <- rep(0, (d0+1))
      for (i in 1:(d0+1)) {
        lag.freq[i] <- sum(par.set[1:igb, ncol0] == (i-1))
      }
      lag.freq <- t(matrix(lag.freq, dimnames = list(c(as.character(0:d0)), c("Frec."))))
      cat("Escogencia del Rezago : ", "\n")
      print(lag.freq)
      cat("------------", "\n")
    }
  }   ### fin del igb
  
  
  mcmc.stat <- tar2e.summaryx(par.set[(Burnin + 1):Iteration, 1:(ncol0 - 1)], lagp1, lagp2, lagP1, lagP2, lagq1, lagq2, constant)
  print(round(mcmc.stat, 4))
  
  lag.y <- c(0:d0)
  lag.d <- lag.y[lag.freq == max(lag.freq)]
  cat("Escogencia del Rezago : ", "\n")
  print(lag.freq)
  cat("------------", "\n")
  cat("La probabilidad a posterior más alta corresponde al rezago: ", lag.d, "\n")
  
  
  loglik.2<-tar2e.likx(x, p1, p2, P1, P2, q1, q2, mcmc.stat[1:(p1+constant), 1], mcmc.stat[(p1+constant+1):(p1+constant+P1), 1], mcmc.stat[(p1+constant+P1+1):(p1+constant+P1+q1), 1],mcmc.stat[(p1+constant+P1+q1+1):(p1+constant+P1+q1+p2+constant), 1],  mcmc.stat[(p1+constant+P1+q1+p2+constant+1):(p1+constant+P1+q1+p2+constant+P2), 1], mcmc.stat[(p1+constant+P1+q1+p2+constant+P2+1):(p1+constant+P1+q1+p2+constant+P2+q2), 1],mcmc.stat[p1+constant+P1+q1+p2+constant+P2+q2+1, 1], mcmc.stat[p1+constant+P1+q1+p2+constant+P2+q2+2, 1], lag.d, mcmc.stat[p1+constant+P1+q1+p2+constant+P2+q2+3, 1], lagp1, lagp2, lagP1, lagP2, lagq1, lagq2,constant, thresVar, s )
  
  DIC<- (2*(-2*sum(loglik.1[(Burnin + 1):Iteration]))/length(loglik.1[(Burnin + 1):Iteration])) - (-2*loglik.2)
  cat(" DIC = ", DIC, "\n")
  
  #lnapriorisfijo<-NA
  #lnapriorisfijo<- -0.5*((p1+constant)*log(2*pi)+(p1+constant)*log(det(solve(v0ph1)))+ t(mcmc.stat[1:(p1 + constant), 1])%*%v0ph1%*%( mcmc.stat[1:(p1  + constant), 1]))-0.5*(P1*log(2*pi)+P1*log(det(solve(v0PH1)))+ t(mcmc.stat[(p1+constant+1):(p1+constant+P1), 1])%*%v0PH1%*%(mcmc.stat[(p1+constant+1):(p1+constant+P1), 1]))-0.5*(q1*log(2*pi)+q1*log(det(solve(v0qh1)))+ t(mcmc.stat[(p1+constant+P1+1):(p1+constant+P1+q1), 1])%*%v0qh1%*%(mcmc.stat[(p1+constant+P1+1):(p1+constant+P1+q1), 1]))-0.5*((p2+constant)*log(2*pi)+(p2+constant)*log(det(solve(v0ph2)))+ t(mcmc.stat[(p1+constant+P1+q1+1):(p1+constant+P1+q1+p2+constant), 1])%*%v0ph2%*%(mcmc.stat[(p1+constant+P1+q1+1):(p1+constant+P1+q1+p2+constant), 1]))-0.5*(P2*log(2*pi)+P2*log(det(solve(v0PH2)))+ t(mcmc.stat[(p1+constant+P1+q1+p2+constant+1):(p1+constant+P1+q1+p2+constant+P2), 1])%*%v0PH2%*%(mcmc.stat[(p1+constant+P1+q1+p2+constant+1):(p1+constant+P1+q1+p2+constant+P2), 1]))-0.5*(q2*log(2*pi)+q2*log(det(solve(v0qh2)))+ t(mcmc.stat[(p1+constant+P1+q1+p2+constant+P2+1):(p1+constant+P1+q1+p2+constant+P2+q2), 1])%*%v0qh2%*%(mcmc.stat[(p1+constant+P1+q1+p2+constant+P2+1):(p1+constant+P1+q1+p2+constant+P2+q2), 1]))+(1.5*log(var(x)/2)-log(gamma(1.5))-2.5*log(mcmc.stat[( mcmc.stat[p1+constant+P1+q1+p2+constant+P2+q2+1, 1]), 1])-0.5*var(x)*(1/mcmc.stat[( mcmc.stat[p1+constant+P1+q1+p2+constant+P2+q2+1, 1]), 1]))+(1.5*log(var(x)/2)-log(gamma(1.5))-2.5*log(mcmc.stat[( mcmc.stat[p1+constant+P1+q1+p2+constant+P2+q2+2, 1]), 1])-0.5*var(x)*(1/mcmc.stat[( mcmc.stat[p1+constant+P1+q1+p2+constant+P2+q2+2, 1]), 1]))+log(1/(bound.thv[2]-bound.thv[1]))+log(1/(d0+1))
  
  
  
  
  if (constant==1){
    
    con.1 <-  mcmc.stat[1, 1]
    parp.1 <- mcmc.stat[2:(p1+ constant), 1]
    parP.1 <- mcmc.stat[(p1+constant+1):(p1+constant+P1), 1]
    parq.1 <- mcmc.stat[(p1+constant+P1+1):(p1+constant+P1+q1), 1]
    
    con.2 <-  mcmc.stat[p1+constant+P1+q1+1, 1]
    parp.2 <- mcmc.stat[(p1+constant+P1+q1+1+1):(p1+constant+P1+q1+p2+constant), 1]
    parP.2 <- mcmc.stat[(p1+constant+P1+q1+p2+constant+1):(p1+constant+P1+q1+p2+constant+P2), 1]
    parq.2 <- mcmc.stat[(p1+constant+P1+q1+p2+constant+P2+1):(p1+constant+P1+q1+p2+constant+P2+q2), 1]
    
    sig.1u <- mcmc.stat[p1+constant+P1+q1+p2+constant+P2+q2+1,1]
    sig.2d <- mcmc.stat[p1+constant+P1+q1+p2+constant+P2+q2+2,1]
    
    thv   <-  mcmc.stat[p1+constant+P1+q1+p2+constant+P2+q2+3, 1]
    
  }
  
  else {
    
    con.1 <- 0 
    parp.1 <- mcmc.stat[1:p1, 1]
    parP.1 <- mcmc.stat[(p1+1):(p1+P1), 1]
    parq.1 <- mcmc.stat[(p1+P1+1):(p1+P1+q1), 1]
    
    con.2 <- 0 
    parp.2 <- mcmc.stat[(p1+P1+q1+1):(p1+P1+q1+p2), 1]
    parP.2 <- mcmc.stat[(p1+P1+q1+p2+1):(p1+P1+q1+p2+P2), 1]
    parq.2 <- mcmc.stat[(p1+P1+q1+p2+P2+1):(p1+P1+q1+p2+P2+q2), 1]
    
    sig.1u <- mcmc.stat[p1+P1+q1+p2+P2+q2+1,1]
    sig.2d <- mcmc.stat[p1+P1+q1+p2+P2+q2+2,1]
    
    thv   <-  mcmc.stat[p1+P1+q1+p2+P2+q2+3, 1]
    
  }
  
  
  maxd <- max(max(lagp1)+s*max(lagP1), max(lagp2)+s*max(lagP2), max(lagq1), max(lagq2))
  
  residual <-residual.est<- rep(0, (nx - maxd))
  residual1 <- residual2<- rep(0, (nx - maxd))
  
  multipP1<-matrix(NA,nrow=(nx-maxd), ncol=p1*P1)
  multipP2<-matrix(NA,nrow=(nx-maxd), ncol=p2*P2)
  
  for (t in (maxd + 1):nx) {
    
    if (thresVar[t - lag.d] <= thv) {
      
      for (i in 1:P1){
        for (j in 1:p1){
          multipP1[t-maxd, (i*j+(p1-j)*(i-1))]<-parP.1[i]*parp.1[j]*x[t-(lagp1[j]+s*lagP1[i])]
        }
      }
      
      residual[t - maxd] <- (x[t] - sum(con.1, parp.1[1:p1]*x[t - lagp1], parP.1[1:P1]*x[t - s*lagP1], -multipP1[t-maxd, ],  parq.1[1:q1]*thresVar[t - lagq1]))
      residual.est[t - maxd]<-residual[t - maxd]/sqrt(sig.1u)
      residual1[t - maxd] <- (x[t] - sum(con.1, parp.1[1:p1]*x[t - lagp1], parP.1[1:P1]*x[t - s*lagP1], - multipP1[t-maxd, ],  parq.1[1:q1]*thresVar[t - lagq1]))
    }
    else {
      
      for (i in 1:P2){
        for (j in 1:p2){
          multipP2[t-maxd, (i*j+(p2-j)*(i-1))]<-parP.2[i]*parp.2[j]*x[t-(lagp2[j]+s*lagP2[i])]
        }
      }
      
      residual[t - maxd] <- (x[t] - sum(con.2, parp.2[1:p2]*x[t - lagp2], parP.2[1:P2]*x[t - s*lagP2],  -multipP2[t-maxd, ],  parq.2[1:q2]*thresVar[t - lagq2]))
      residual.est[t - maxd]<-residual[t - maxd]/sqrt(sig.2d)
      residual2[t - maxd] <- (x[t] - sum(con.2, parp.2[1:p2]*x[t - lagp2], parP.2[1:P2]*x[t - s*lagP2], -multipP2[t-maxd, ],  parq.2[1:q2]*thresVar[t - lagq2]))
    }
    
  }
  res1<-sum(residual1^2)
  res2<-sum(residual2^2)
  lag.yy<-thresVar[(maxd+1-lag.d):(nx-lag.d)]
  n1<-sum(lag.yy<=thv)
  n2<-sum(lag.yy>thv)
  NAIC<-NA
  NAIC<-((n1*log(res1/n1)+2*(p1+constant+P1+q1)) + (n2*log(res2/n2)+2*(p2+constant+P2+q2)))/(n1+n2)
  cat("NAIC", NAIC,"\n")
  
  
  
  
  tar <- list(mcmc = par.set, posterior = par.set[(Burnin + 1):Iteration, 1:ncol0], coef.par = round(mcmc.stat, 4), residual = residual, residual.est=residual.est, lagd = lag.d, DIC = DIC, NAIC=NAIC, logverosimil=loglik.1[(Burnin+1):Iteration], log.ver=logvermarg[(Burnin+1):Iteration] )
  
  return(tar)
}



################################################################




##########################################



############## INICIO DEL PROGRAMA 3 REGÍMENES





####################  EstimaciÓn de los coeficientes autorregresivos y exÓgenos      
########################    tar3e.coeffxph


tar3e.coeffxph=function(reg, ay, p, P, q, sig, lagd, thres.1, thres.2, mu0ph, v0ph, PH, qh, lagp1, lagp2, lagp3, lagP1, lagP2, lagP3, lagq1, lagq2, lagq3, constant, thresVar, s) 
{
  P11 <- max(max(lagp1)+s*max(lagP1), max(lagp2)+s*max(lagP2),  max(lagp3)+s*max(lagP3), max(lagq1), max(lagq2), max(lagq3)) 
  n <- length(ay)
  lag.y <- thresVar[(P11 + 1 - lagd):(n - lagd)]
  yt <- ay[(P11 + 1):n]
  xxx.1<-vector("list",P)
  txxx.1<-vector("list",P)
  PH.1<-matrix(PH, nrow=P, ncol=1)
  qh.1<-matrix(qh, nrow=q, ncol=1)
  
  L<-matrix(NA, nrow=P, ncol=(n-P11))
  Q<-matrix(NA, nrow=q, ncol=(n-P11))
  xx.1 <- matrix(NA, nrow = p, ncol = (n-P11))
  for (j in 1:P){
    xxx.1[[j]]<-matrix(NA, nrow = p, ncol = (n-P11))
  }
  for (j in 1:P){
    txxx.1[[j]]<-matrix(NA, nrow =(n-P11), ncol =p )
  }
  
  if (reg == 1) {
    
    for (i in 1:p){
      xx.1[i, ] <- ay[(P11-lagp1[i]+1):(n-lagp1[i])]
    }
    txx.1<-t(xx.1)
    for (j in 1:P){
      for (i in 1:p) {
        xxx.1[[j]][i,] <- ay[(P11-lagp1[i]-lagP1[j]*s+1):(n-lagp1[i]-lagP1[j]*s)]*PH[j]
      }
    }
    for (j in 1:P) {
      txxx.1[[j]]<-t(xxx.1[[j]])
    }
    auxsuma<-matrix(0, nrow=nrow(txxx.1[[1]]) , ncol=p)
    
    for (k in 1:P){
      auxsuma<-auxsuma+txxx.1[[k]]
    }
    x.1t<-txx.1-auxsuma
    x.1<-t(x.1t)
    
    if (p==1){
      if (constant==1){
        tx <- cbind(1,t(t(x.1[,lag.y<=thres.1])))
      }
      else {
        tx<- t(t(x.1[,lag.y<=thres.1]))
      }
    }
    if (p>1){
      if (constant==1){
        
        tx <- cbind(1, t(x.1[,lag.y<=thres.1]))
      }
      else {
        tx<- t(x.1[,lag.y<=thres.1])
      }
    }
    
    for (i in 1:P){
      L[i,]<-ay[(P11-lagP1[i]*s+1):(n-lagP1[i]*s)]
    }
    
    for (i in 1:q){
      Q[i,]<-thresVar[(P11-lagq1[i]+1):(n-lagq1[i])]
    }
    
    Ytt<-yt-(t(L)%*%PH.1+t(Q)%*%qh.1)
    Yt<-matrix(Ytt[lag.y<=thres.1], ncol=1)
    sigma<-(t(tx)%*%tx)/sig + v0ph
    mu<-solve(sigma,(t(tx)%*%Yt)/sig + v0ph %*% mu0ph)
    ph<-rmvnorm(1,mu,solve(sigma),method = "chol")
  }
  
  if (reg == 2) {
    
    for (i in 1:p){
      xx.1[i, ] <- ay[(P11-lagp2[i]+1):(n-lagp2[i])]
    }
    txx.1<-t(xx.1)
    for (j in 1:P){
      for (i in 1:p) {
        xxx.1[[j]][i,] <- ay[(P11-lagp2[i]-lagP2[j]*s+1):(n-lagp2[i]-lagP2[j]*s)]*PH[j]
      }
    }
    for (j in 1:P) {
      txxx.1[[j]]<-t(xxx.1[[j]])
    }
    auxsuma<-matrix(0, nrow=nrow(txxx.1[[1]]) , ncol=p)
    
    for (k in 1:P){
      auxsuma<-auxsuma+txxx.1[[k]]
    }
    x.1t<-txx.1-auxsuma
    x.1<-t(x.1t)
    
    if (p==1){
      if (constant==1){
        tx <- cbind(1,t(t(x.1[,(lag.y>thres.1 & lag.y<=thres.2)])))
      }
      else {
        tx<- t(t(x.1[,(lag.y>thres.1 & lag.y<=thres.2)]))
      }
    }
    if (p>1){
      if (constant==1){
        
        tx <- cbind(1, t(x.1[,(lag.y>thres.1 & lag.y<=thres.2)]))
      }
      else {
        tx<- t(x.1[,(lag.y>thres.1 & lag.y<=thres.2)])
      }
    }
    
    
    for (i in 1:P){
      L[i,]<-ay[(P11-lagP2[i]*s+1):(n-lagP2[i]*s)]
    }
    
    for (i in 1:q){
      Q[i,]<-thresVar[(P11-lagq2[i]+1):(n-lagq2[i])]
    }
    
    Ytt<-yt-(t(L)%*%PH.1+t(Q)%*%qh.1)
    Yt<-matrix(Ytt[lag.y>thres.1 & lag.y<=thres.2], ncol=1)
    sigma<-(t(tx)%*%tx)/sig + v0ph
    mu<-solve(sigma,(t(tx)%*%Yt)/sig + v0ph %*% mu0ph)
    ph<-rmvnorm(1,mu,solve(sigma),method = "chol")
  }
  
  if (reg==3) {
    
    for (i in 1:p) {
      xx.1[i, ] <- ay[(P11-lagp3[i]+1):(n-lagp3[i])]
    }
    txx.1<-t(xx.1)
    for (j in 1:P) {
      for (i in 1:p) {
        xxx.1[[j]][i,] <- ay[(P11-lagp3[i]-lagP3[j]*s+1):(n-lagp3[i]-lagP3[j]*s)]*PH[j]
      }
    }
    for (j in 1:P) {
      txxx.1[[j]]<-t(xxx.1[[j]])
    }
    auxsuma<-matrix(0, nrow=nrow(txxx.1[[1]]) , ncol=p)
    
    for (k in 1:P){
      auxsuma<-auxsuma+txxx.1[[k]]
    }
    x.1t<-txx.1-auxsuma
    
    x.1<-t(x.1t)
    if (p==1){
      if (constant==1){
        tx <- cbind(1,t(t(x.1[,lag.y>thres.2])))
      }
      else {
        tx<- t(t(x.1[,lag.y>thres.2]))
      }
    }
    if (p>1){
      if (constant==1){
        
        tx <- cbind(1, t(x.1[,lag.y>thres.2]))
      }
      else {
        tx<- t(x.1[,lag.y>thres.2])
      }
    }
    
    
    
    for (i in 1:P){
      L[i,]<-ay[(P11-lagP3[i]*s+1):(n-lagP3[i]*s)]
    }
    
    for (i in 1:q){
      Q[i,]<-thresVar[(P11-lagq3[i]+1):(n-lagq3[i])]
    }
    
    Ytt<-yt-(t(L)%*%PH.1+t(Q)%*%qh.1)
    Yt<-matrix(Ytt[lag.y>thres.2], ncol=1)
    sigma<-(t(tx)%*%tx)/sig + v0ph
    mu<-solve(sigma,(t(tx)%*%Yt)/sig + v0ph%*%mu0ph)
    ph<-rmvnorm(1,mu,solve(sigma),method="chol")
  }
  return(ph)
}

#################################################################
#################################################


#################### EstimaciÓn de los coeficientes autorregresivos y exÓgenos      
########################    tar3e.coeffxPH


tar3e.coeffxPH=function(reg, ay, p, P, q, sig, lagd, thres.1, thres.2, mu0PH, v0PH, ph, qh, lagp1, lagp2, lagp3, lagP1, lagP2, lagP3, lagq1, lagq2, lagq3, constant, thresVar, s) 
{
  P11 <- max(max(lagp1)+s*max(lagP1), max(lagp2)+s*max(lagP2),  max(lagp3)+s*max(lagP3), max(lagq1), max(lagq2), max(lagq3)) 
  n <- length(ay)
  lag.y <- thresVar[(P11 + 1 - lagd):(n - lagd)]
  yt <- ay[(P11 + 1):n]
  xxx.1<-vector("list",p)
  txxx.1<-vector("list",p)
  ph.1<-matrix(ph, nrow=p+constant, ncol=1)
  qh.1<-matrix(qh, nrow=q, ncol=1)
  
  L<-matrix(NA, nrow=p, ncol=(n-P11))
  Q<-matrix(NA, nrow=q, ncol=(n-P11))
  xx.1 <- matrix(NA, nrow = P, ncol = (n-P11))
  for (j in 1:p){
    xxx.1[[j]]<-matrix(NA, nrow = P, ncol = (n-P11))
  }
  for (j in 1:p){
    txxx.1[[j]]<-matrix(NA, nrow =(n-P11), ncol =P)
  }
  if (reg == 1) {
    
    for (i in 1:P){
      xx.1[i, ] <- ay[(P11-lagP1[i]*s+1):(n-lagP1[i]*s)]
    }
    txx.1<-t(xx.1)
    for (j in 1:p){
      for (i in 1:P) {
        xxx.1[[j]][i,] <- ay[(P11-lagP1[i]*s-lagp1[j]+1):(n-lagP1[i]*s-lagp1[j])]*ph[j+constant]
      }
    }
    for (j in 1:p) {
      txxx.1[[j]]<-t(xxx.1[[j]])
    }
    auxsuma<-matrix(0, nrow=nrow(txxx.1[[1]]) , ncol=P)
    
    for (k in 1:p){
      auxsuma<-auxsuma+txxx.1[[k]]
    }
    
    x.1t<-txx.1-auxsuma
    x.1<-t(x.1t)
    
    if (P==1){
      tx <- t(t(x.1[,lag.y<=thres.1]))
    }
    
    if (P>1){
      tx <- t(x.1[,lag.y<=thres.1])
    }
    
    
    for (i in 1:p){
      L[i,]<-ay[(P11-lagp1[i]+1):(n-lagp1[i])]
    }
    if (constant==1){
      L<-cbind(1,t(L))
    }
    else {
      L<-t(L)
    }
    for (i in 1:q){
      Q[i,]<-thresVar[(P11-lagq1[i]+1):(n-lagq1[i])]
    }
    
    Ytt<-yt-(L%*%ph.1+t(Q)%*%qh.1)
    Yt<-matrix(Ytt[lag.y<=thres.1], ncol=1)
    sigma<-(t(tx)%*%tx)/sig + v0PH
    mu<-solve(sigma,(t(tx)%*%Yt)/sig + v0PH %*% mu0PH)
    PH<-rmvnorm(1,mu,solve(sigma),method = "chol")
  }
  
  if (reg == 2) {
    
    for (i in 1:P){
      xx.1[i, ] <- ay[(P11-lagP2[i]*s+1):(n-lagP2[i]*s)]
    }
    txx.1<-t(xx.1)
    for (j in 1:p){
      for (i in 1:P) {
        xxx.1[[j]][i,] <- ay[(P11-lagP2[i]*s-lagp2[j]+1):(n-lagP2[i]*s-lagp2[j])]*ph[j+constant]
      }
    }
    for (j in 1:p) {
      txxx.1[[j]]<-t(xxx.1[[j]])
    }
    auxsuma<-matrix(0, nrow=nrow(txxx.1[[1]]) , ncol=P)
    for (k in 1:p){
      auxsuma<-auxsuma+txxx.1[[k]]
    }
    x.1t<-txx.1-auxsuma
    x.1<-t(x.1t)
    
    if (P==1){
      tx <- t(t(x.1[,(lag.y>thres.1 & lag.y<=thres.2)]))
    }
    
    if (P>1){
      tx <- t(x.1[,(lag.y>thres.1 & lag.y<=thres.2)])
    }
    
    for (i in 1:p){
      L[i,]<-ay[(P11-lagp2[i]+1):(n-lagp2[i])]
    }
    if (constant==1){
      L<-cbind(1,t(L))
    }
    else {
      L<-t(L)
    }
    for (i in 1:q){
      Q[i,]<-thresVar[(P11-lagq2[i]+1):(n-lagq2[i])]
    }
    
    Ytt<-yt-(L%*%ph.1+t(Q)%*%qh.1)
    Yt<-matrix(Ytt[lag.y>thres.1 & lag.y<=thres.2], ncol=1)
    sigma<-(t(tx)%*%tx)/sig + v0PH
    mu<-solve(sigma,(t(tx)%*%Yt)/sig + v0PH %*% mu0PH)
    PH<-rmvnorm(n = 1,mu,solve(sigma),method = "chol")
  }
  
  
  if (reg==3) {
    
    for (i in 1:P){
      xx.1[i, ] <- ay[(P11-lagP3[i]*s+1):(n-lagP3[i]*s)]
    }
    txx.1<-t(xx.1)
    for (j in 1:p){
      for (i in 1:P) {
        xxx.1[[j]][i,] <- ay[(P11-lagP3[i]*s-lagp3[j]+1):(n-lagP3[i]*s-lagp3[j])]*ph[j+constant]
      }
    }
    for (j in 1:p) {
      txxx.1[[j]]<-t(xxx.1[[j]])
    }
    
    auxsuma<-matrix(0, nrow=nrow(txxx.1[[1]]) , ncol=P)
    
    for (k in 1:p){
      auxsuma<-auxsuma+txxx.1[[k]]
    }
    x.1t<-txx.1-auxsuma
    x.1<-t(x.1t)
    
    if (P==1){
      tx <- t(t(x.1[,lag.y>thres.2]))
    }
    
    if (P>1){
      tx <- t(x.1[,lag.y>thres.2])
    }
    
    for (i in 1:p){
      L[i,]<-ay[(P11-lagp3[i]+1):(n-lagp3[i])]
    }
    if (constant==1){
      L<-cbind(1,t(L))
    }
    else {
      L<-t(L)
    }
    
    for (i in 1:q){
      Q[i,]<-thresVar[(P11-lagq3[i]+1):(n-lagq3[i])]
    }
    
    Ytt<-yt-(L%*%ph.1+t(Q)%*%qh.1)
    Yt<-matrix(Ytt[lag.y>thres.2], ncol=1)
    sigma<-(t(tx)%*%tx)/sig + v0PH
    mu<-solve(sigma,(t(tx)%*%Yt)/sig + v0PH %*% mu0PH)
    PH<-rmvnorm(1,mu,solve(sigma),method = "chol")
  }
  return(PH)
}

#################################################################
#################################################

####################  EstimaciÓn de los coeficientes autorregresivos y exÓgenos      
########################    tar3e.coeffxqh


tar3e.coeffxqh=function(reg, ay, p, P, q, sig, lagd, thres.1, thres.2, mu0qh, v0qh, ph, PH, lagp1, lagp2, lagp3, lagP1, lagP2, lagP3, lagq1, lagq2, lagq3, constant, thresVar, s) 
{
  P11 <- max(max(lagp1)+s*max(lagP1), max(lagp2)+s*max(lagP2), max(lagp3)+s*max(lagP3), max(lagq1), max(lagq2), max(lagq3)) 
  n <- length(ay)
  lag.y <- thresVar[(P11 + 1 - lagd):(n - lagd)]
  yt <- ay[(P11 + 1):n]
  ph.1<-matrix(ph, nrow=p+constant, ncol=1)
  PH.1<-matrix(PH, nrow=P, ncol=1)
  A<-matrix(NA, nrow=P*(s-1), ncol=(n-P11))
  L<-matrix(NA, nrow=p, ncol=(n-P11))
  Q<-matrix(NA, nrow=P, ncol=(n-P11))
  x.1 <- matrix(NA, nrow = q, ncol = (n-P11))
  yy=vector("list", P)
  for (j in 1:P){
    yy[[j]]<-matrix(NA, nrow=(s-1), ncol=(n-P11))
  }
  coefaux<- matrix(NA, nrow = P*(s-1), ncol =1)
  xx=vector("list", P)
  for (j in 1:P){
    xx[[j]]<-matrix(NA, nrow=(s-1), ncol=1)
  }
  
  
  for (i in 1:P){
    
    xx[[i]][1:(s-p-1),]<-rep(0,(s-p-1))
    
    xx[[i]][(s-p):(s-1), ]<- -ph[(1+constant):(p+constant)]*PH[i]
    
  }
  
  for (j in 1:P){
    coefaux[((j-1)*(s-p-1)+(j-1)*p+1):(j*(s-p-1)+(j-1)*p),]<-xx[[j]][1:(s-p-1),] 
    coefaux[(j*(s-p-1)+(j-1)*p+1):(j*(s-p-1)+j*p),]<- xx[[j]][(s-p):(s-1), ]
  }
  
  
  
  if (reg == 1) {
    
    for (i in 1:q){
      x.1[i, ] <- thresVar[(P11-lagq1[i]+1):(n-lagq1[i])]
    }
    if (q==1){
      tx<- t(t(x.1[ ,lag.y<=thres.1]))
    }
    if (q>1){
      tx<- t(x.1[ ,lag.y<=thres.1])
    }
    
    for (i in 1:p){
      L[i,]<-ay[(P11-lagp1[i]+1):(n-lagp1[i])]
    }
    if (constant==1){
      L<-cbind(1,t(L))
    }
    else {
      L<-t(L)
    }
    
    for (i in 1:P){
      Q[i,]<-ay[(P11-lagP1[i]*s+1):(n-lagP1[i]*s)]
    }
    for (j in 1:P){
      for (i in 1:(s-p-1)){
        yy[[j]][i,]<-ay[(P11-((j-1)*s+p+i)+1):(n-((j-1)*s+p+i))]
      }
      for (k in (s-p-1+1):(s-1)){
        yy[[j]][k, ]<-ay[(P11-(j*s+ k-(s-p-1))+1):(n-(j*s+k-(s-p-1)))]
      }
    }
    for (j in 1:P){
      A[((j-1)*(s-p-1)+(j-1)*p+1):(j*(s-p-1)+(j-1)*p),]<- yy[[j]][1:(s-p-1),]
      A[(j*(s-p-1)+(j-1)*p+1):(j*(s-p-1)+j*p),]<- yy[[j]][(s-p-1+1):(s-1),]
    }
    Ytt<-yt-(t(A)%*%coefaux+L%*%ph.1+t(Q)%*%PH.1)
    Yt<-matrix(Ytt[lag.y<=thres.1], ncol=1)
    sigma<-(t(tx)%*%tx)/sig + v0qh
    mu<-solve(sigma,(t(tx)%*%Yt)/sig + v0qh %*% mu0qh)
    qh<-rmvnorm(1,mu,solve(sigma),method = "chol")
  }
  
  if (reg == 2) {
    
    for (i in 1:q){
      x.1[i, ] <- thresVar[(P11-lagq2[i]+1):(n-lagq2[i])]
    }
    if (q==1){
      tx<- t(t(x.1[ ,(lag.y>thres.1 & lag.y<=thres.2)]))
    }
    if (q>1){
      tx<- t(x.1[ ,(lag.y>thres.1 & lag.y<=thres.2)])
    }
    
    
    for (i in 1:p){
      L[i,]<-ay[(P11-lagp2[i]+1):(n-lagp2[i])]
    }
    if (constant==1){
      L<-cbind(1,t(L))
    }
    else {
      L<-t(L)
    }
    
    for (i in 1:P){
      Q[i,]<-ay[(P11-lagP2[i]*s+1):(n-lagP2[i]*s)]
    }
    for (j in 1:P){
      for (i in 1:(s-p-1)){
        yy[[j]][i,]<-ay[(P11-((j-1)*s+p+i)+1):(n-((j-1)*s+p+i))]
      }
      for (k in (s-p-1+1):(s-1)){
        yy[[j]][k, ]<-ay[(P11-(j*s+ k-(s-p-1))+1):(n-(j*s+k-(s-p-1)))]
      }
    }
    for (j in 1:P){
      A[((j-1)*(s-p-1)+(j-1)*p+1):(j*(s-p-1)+(j-1)*p),]<- yy[[j]][1:(s-p-1),]
      A[(j*(s-p-1)+(j-1)*p+1):(j*(s-p-1)+j*p),]<- yy[[j]][(s-p-1+1):(s-1),]
    }
    
    
    Ytt<-yt-(t(A)%*%coefaux+L%*%ph.1+t(Q)%*%PH.1)
    Yt<-matrix(Ytt[lag.y>thres.1 & lag.y<=thres.2], ncol=1)
    sigma<-(t(tx)%*%tx)/sig + v0qh
    mu<-solve(sigma,(t(tx)%*%Yt)/sig + v0qh %*% mu0qh)
    qh<-rmvnorm(1,mu,solve(sigma),method = "chol")
  }
  
  
  if (reg == 3) {
    
    for (i in 1:q){
      x.1[i, ] <- thresVar[(P11-lagq3[i]+1):(n-lagq3[i])]
    }
    if (q==1){
      tx<- t(t(x.1[ ,lag.y>thres.2]))
    }
    if (q>1){
      tx<- t(x.1[ ,lag.y>thres.2])
    }
    
    
    for (i in 1:p){
      L[i,]<-ay[(P11-lagp3[i]+1):(n-lagp3[i])]
    }
    if (constant==1){
      L<-cbind(1,t(L))
    }
    else {
      L<-t(L)
    }
    
    for (i in 1:P){
      Q[i,]<-ay[(P11-lagP3[i]*s+1):(n-lagP3[i]*s)]
    }
    for (j in 1:P){
      for (i in 1:(s-p-1)){
        yy[[j]][i,]<-ay[(P11-((j-1)*s+p+i)+1):(n-((j-1)*s+p+i))]
      }
      for (k in (s-p-1+1):(s-1)){
        yy[[j]][k, ]<-ay[(P11-(j*s+ k-(s-p-1))+1):(n-(j*s+k-(s-p-1)))]
      }
    }
    for (j in 1:P){
      A[((j-1)*(s-p-1)+(j-1)*p+1):(j*(s-p-1)+(j-1)*p),]<- yy[[j]][1:(s-p-1),]
      A[(j*(s-p-1)+(j-1)*p+1):(j*(s-p-1)+j*p),]<- yy[[j]][(s-p-1+1):(s-1),]
    }
    
    
    Ytt<-yt-(t(A)%*%coefaux+L%*%ph.1+t(Q)%*%PH.1)
    Yt<-matrix(Ytt[lag.y>thres.2], ncol=1)
    sigma<-(t(tx)%*%tx)/sig + v0qh
    mu<-solve(sigma,(t(tx)%*%Yt)/sig + v0qh %*% mu0qh)
    qh<-rmvnorm(1,mu,solve(sigma),method = "chol")
  }
  return(qh)
}

#################################################################
#################################################



############### Extraer la varianza de la distribución de los errores      
##################  tar3e.sigmax

tar3e.sigmax=function(reg, ay, thres.1, thres.2,  lagd, p, P, q, ph, PH, qh, v, lambda, lagp1, lagp2, lagp3, lagP1, lagP2, lagP3, lagq1, lagq2, lagq3, constant, thresVar, s)
{
  P11 <- max(max(lagp1)+s*max(lagP1), max(lagp2)+s*max(lagP2), max(lagp3)+s*max(lagP3), max(lagq1), max(lagq2), max(lagq3) ) 
  n <- length(ay)
  lag.y <- thresVar[(P11 + 1 - lagd):(n - lagd)]
  yt <- ay[(P11 + 1):n]
  x.1 <- matrix(0, nrow = p+s*P+q, ncol = (n - P11))
  x.11<-matrix(NA, nrow = p, ncol = (n-P11))
  x.12<-matrix(NA, nrow = P, ncol = (n-P11))
  x.13<-vector("list",P)
  for (j in 1:P){
    x.13[[j]]<-matrix(NA, nrow = p, ncol = (n-P11))
  }
  x.14<-matrix(NA, nrow = q, ncol = (n-P11))
  
  p.1<-matrix(0,nrow=p+s*P+q+constant,ncol=1)
  ph<-matrix(ph,nrow=p+constant,ncol=1)
  PH<-matrix(PH,nrow=P,ncol=1)
  qh<-matrix(qh, nrow=q,ncol=1)
  for (i in 1:(p+constant)){
    p.1[i]<-ph[i]
  }
  for (i in 1:P){
    p.1[i*s+constant]<-PH[i]
  }
  for (i in 1:P){
    for (j in 1:p){
      p.1[i*s+j+constant]<- -ph[j+constant]*PH[i]
    }
  }
  for (i in 1:q){
    p.1[p+s*P+constant+i]<-qh[i]
  }
  
  if (reg == 1) {
    m <- sum(lag.y <= thres.1)
    y<- matrix(yt[lag.y <= thres.1], ncol = 1)
    for (i in 1:p){
      x.11[i,]<-ay[(P11 - lagp1[i] + 1):(n - lagp1[i])] 
    }
    x.1[1:p,]<-x.11
    for (i in 1:P){
      x.12[i,]<-ay[(P11 - lagP1[i]*s + 1):(n - lagP1[i]*s)]
    }
    x.1[seq(s,P*s,s),]<-x.12
    for (i in 1:P){
      for (j in 1:p){
        x.13[[i]][j,]<-ay[(P11 - (lagp1[j]+s*lagP1[i]) + 1):(n -(lagp1[j]+s*lagP1[i]))]
      }
    }
    for (i in 1:P){ 
      x.1[seq(i*s+1,i*s+p,1),]<-x.13[[i]]
    }
    for (i in 1:q) {
      x.14[i, ] <- thresVar[(P11 - lagq1[i] + 1):(n - lagq1[i])]
    }
    x.1[(p+s*P+1):(p+s*P+q),]<-x.14
    if (constant == 1) {
      tx <- cbind(1, t(x.1[,lag.y <= thres.1]))
    }
    else {
      tx <- t(x.1[,lag.y <= thres.1])
    }
    s2 <- (t(y-tx%*%p.1)%*%(y-tx%*%p.1))/m
    
  }
  
  if (reg==2) {
    m <- sum(lag.y>thres.1 & lag.y<=thres.2)
    y<- matrix(yt[lag.y>thres.1 & lag.y<=thres.2], ncol = 1)
    for (i in 1:p){
      x.11[i,]<-ay[(P11 - lagp2[i] + 1):(n - lagp2[i])] 
    }
    x.1[1:p,]<-x.11
    for (i in 1:P){
      x.12[i,]<-ay[(P11 - lagP2[i]*s + 1):(n - lagP2[i]*s)]
    }
    x.1[seq(s,P*s,s),]<-x.12
    for (i in 1:P){
      for (j in 1:p){
        x.13[[i]][j,]<-ay[(P11 - (lagp2[j]+s*lagP2[i]) + 1):(n -(lagp2[j]+s*lagP2[i]))]
      }
    }
    for (i in 1:P){ 
      x.1[seq(i*s+1,i*s+p,1),]<-x.13[[i]]
    }
    for (i in 1:q) {
      x.14[i, ] <- thresVar[(P11 - lagq2[i] + 1):(n - lagq2[i])]
    }
    x.1[(p+s*P+1):(p+s*P+q),]<-x.14
    
    if (constant == 1) {
      tx <- cbind(1, t(x.1[, (lag.y>thres.1 & lag.y<=thres.2)]))
    }
    else {
      tx <- t(x.1[, (lag.y>thres.1 & lag.y<=thres.2)])
    }
    
    s2 <- (t(y-tx%*%p.1)%*%(y-tx%*%p.1))/m
    
  }
  
  
  
  if (reg==3) {
    m <- sum(lag.y>thres.2)
    y<- matrix(yt[lag.y>thres.2], ncol = 1)
    for (i in 1:p){
      x.11[i,]<-ay[(P11 - lagp3[i] + 1):(n - lagp3[i])] 
    }
    x.1[1:p,]<-x.11
    for (i in 1:P){
      x.12[i,]<-ay[(P11 - lagP3[i]*s + 1):(n - lagP3[i]*s)]
    }
    x.1[seq(s,P*s,s),]<-x.12
    for (i in 1:P){
      for (j in 1:p){
        x.13[[i]][j,]<-ay[(P11 - (lagp3[j]+s*lagP3[i]) + 1):(n -(lagp3[j]+s*lagP3[i]))]
      }
    }
    for (i in 1:P){ 
      x.1[seq(i*s+1,i*s+p,1),]<-x.13[[i]]
    }
    for (i in 1:q) {
      x.14[i, ] <- thresVar[(P11 - lagq3[i] + 1):(n - lagq3[i])]
    }
    x.1[(p+s*P+1):(p+s*P+q),]<-x.14
    
    if (constant == 1) {
      tx <- cbind(1, t(x.1[,lag.y>thres.2]))
    }
    else {
      tx <- t(x.1[,lag.y>thres.2])
    }
    
    s2 <- (t(y-tx%*%p.1)%*%(y-tx%*%p.1))/m
    
  }
  shape <- (v + m)/2
  rate <- (v*lambda + m*s2)/2
  sigma <- 1/rgamma(1, shape, rate)
  return(sigma)
}

#############################################################################
##########################################


###################### calcular la función log.verosimil       
############################ tar3e.likx

tar3e.likx=function(ay, p1, p2, p3, P1, P2, P3, q1, q2, q3, ph.1, PH.1, qh.1, ph.2, PH.2, qh.2, ph.3, PH.3, qh.3, sig.1, sig.2, sig.3, lagd, thres.1, thres.2, lagp1, lagp2, lagp3, lagP1, lagP2, lagP3, lagq1, lagq2, lagq3,  constant, thresVar, s) 
  
{
  P11 <- max(max(lagp1)+s*max(lagP1), max(lagp2)+s*max(lagP2),max(lagp3)+s*max(lagP3), max(lagq1), max(lagq2), max(lagq3)) 
  n <- length(ay)
  lag.y <- thresVar[(P11 + 1 - lagd):(n - lagd)]
  yt <- ay[(P11 + 1):n]
  
  p.1 <- matrix(0, nrow = p1 + s*P1 + q1 + constant, ncol = 1)
  ph1<-matrix(ph.1,nrow=p1+constant,ncol=1)
  PH1<-matrix(PH.1,nrow=P1 ,ncol=1)
  qh1<-matrix(qh.1,nrow=q1,ncol=1)
  
  p.2 <- matrix(0, nrow = p2 + s*P2 + q2 + constant, ncol = 1)
  ph2<-matrix(ph.2,nrow=p2+constant,ncol=1)
  PH2<-matrix(PH.2,nrow=P2,ncol=1)
  qh2<-matrix(qh.2,nrow=q2,ncol=1)
  
  p.3 <- matrix(0, nrow = p3+ s*P3 + q3 + constant, ncol = 1)
  ph3<-matrix(ph.3,nrow=p3+constant,ncol=1)
  PH3<-matrix(PH.3,nrow=P3,ncol=1)
  qh3<-matrix(qh.3,nrow=q3,ncol=1)
  
  
  for (i in 1:(p1+constant)){
    p.1[i]<-ph1[i]
  }
  for (i in 1:P1){
    p.1[i*s+constant]<-PH1[i]
  }
  for (i in 1:P1){
    for (j in 1:p1){
      p.1[i*s+j+constant]<- -ph1[j+constant]*PH1[i]
    }
  }
  for (i in 1:q1){
    p.1[p1+s*P1+constant+i]<-qh1[i]
  }
  
  
  for (i in 1:(p2+constant)){
    p.2[i]<-ph2[i]
  }
  for (i in 1:P2){
    p.2[i*s+constant]<-PH2[i]
  }
  for (i in 1:P2){
    for (j in 1:p2){
      p.2[i*s+j+constant]<- -ph2[j+constant]*PH2[i]
    }
  }
  for (i in 1:q2){
    p.2[p2+s*P2+constant+i]<-qh2[i]
  }
  
  for (i in 1:(p3+constant)){
    p.3[i]<-ph3[i]
  }
  for (i in 1:P3){
    p.3[i*s+constant]<-PH3[i]
  }
  for (i in 1:P3){
    for (j in 1:p3){
      p.3[i*s+j+constant]<- -ph3[j+constant]*PH3[i]
    }
  }
  for (i in 1:q3){
    p.3[p3+s*P3+constant+i]<-qh3[i]
  }
  
  
  x.1 <- matrix(0, nrow = p1+s*P1+q1, ncol = (n - P11))
  x.11<-matrix(NA, nrow = p1, ncol = (n-P11))
  x.12<-matrix(NA, nrow = P1, ncol = (n-P11))
  x.13<-vector("list",P1)
  for (j in 1:P1){
    x.13[[j]]<-matrix(NA, nrow = p1, ncol = (n-P11))
  }
  x.14<-matrix(NA, nrow = q1, ncol = (n-P11))
  
  x.2 <- matrix(0, nrow = p2+s*P2+q2, ncol = (n - P11))
  x.21<-matrix(NA, nrow = p2, ncol = (n-P11))
  x.22<-matrix(NA, nrow = P2, ncol = (n-P11))
  x.23<-vector("list",P2)
  for (j in 1:P2){
    x.23[[j]]<-matrix(NA, nrow = p2, ncol = (n-P11))
  }
  x.24<-matrix(NA, nrow = q2, ncol = (n-P11))
  
  x.3 <- matrix(0, nrow = p3+s*P3+q3, ncol = (n - P11))
  x.31<-matrix(NA, nrow = p3, ncol = (n-P11))
  x.32<-matrix(NA, nrow = P3, ncol = (n-P11))
  x.33<-vector("list",P3)
  for (j in 1:P3){
    x.33[[j]]<-matrix(NA, nrow = p3, ncol = (n-P11))
  }
  x.34<-matrix(NA, nrow = q3, ncol = (n-P11))
  
  n1 <- sum(lag.y <= thres.1)
  n2 <- sum(lag.y>thres.1 & lag.y<=thres.2)
  n3 <- sum(lag.y > thres.2)
  
  y.1 <- matrix(yt[lag.y <= thres.1], ncol = 1)
  y.2 <- matrix(yt[lag.y>thres.1 & lag.y<=thres.2], ncol = 1)
  y.3 <- matrix(yt[lag.y > thres.2], ncol = 1)
  
  for (i in 1:p1){
    x.11[i,]<-ay[(P11 - lagp1[i] + 1):(n - lagp1[i])] 
  }
  x.1[1:p1,]<-x.11
  for (i in 1:P1){
    x.12[i,]<-ay[(P11 - lagP1[i]*s + 1):(n - lagP1[i]*s)]
  }
  x.1[seq(s,P1*s,s),]<-x.12
  for (i in 1:P1){
    for (j in 1:p1){
      x.13[[i]][j,]<-ay[(P11 - (lagp1[j]+s*lagP1[i]) + 1):(n -(lagp1[j]+s*lagP1[i]))]
    }
  }
  for (i in 1:P1){ 
    x.1[seq(i*s+1,i*s+p1,1),]<-x.13[[i]]
  }
  for (i in 1:q1) {
    x.14[i, ] <- thresVar[(P11 - lagq1[i] + 1):(n - lagq1[i])]
  }
  x.1[(p1+s*P1+1):(p1+s*P1+q1),]<-x.14
  if (constant == 1) {
    tx.1 <- cbind(1, t(x.1[ ,lag.y<=thres.1]))
  }
  else {
    tx.1 <- t(x.1[ ,lag.y<=thres.1])
  }
  
  for (i in 1:p2){
    x.21[i,]<-ay[(P11 - lagp2[i] + 1):(n - lagp2[i])] 
  }
  x.2[1:p2,]<-x.21
  for (i in 1:P2){
    x.22[i,]<-ay[(P11 - lagP2[i]*s + 1):(n - lagP2[i]*s)]
  }
  x.2[seq(s,P2*s,s),]<-x.22
  for (i in 1:P2){
    for (j in 1:p2){
      x.23[[i]][j,]<-ay[(P11 - (lagp2[j]+s*lagP2[i]) + 1):(n -(lagp2[j]+s*lagP2[i]))]
    }
  }
  for (i in 1:P2){ 
    x.2[seq(i*s+1,i*s+p2,1),]<-x.23[[i]]
  }
  for (i in 1:q2) {
    x.24[i, ] <- thresVar[(P11 - lagq2[i] + 1):(n - lagq2[i])]
  }
  x.2[(p2+s*P2+1):(p2+s*P2+q2),]<-x.24
  if (constant == 1) {
    tx.2 <- cbind(1, t(x.2[,lag.y>thres.1 & lag.y<=thres.2]))
  }
  else  {
    tx.2 <- t(x.2[,lag.y>thres.1 & lag.y<=thres.2])
  }
  
  for (i in 1:p3){
    x.31[i,]<-ay[(P11 - lagp3[i] + 1):(n - lagp3[i])] 
  }
  x.3[1:p3,]<-x.31
  for (i in 1:P3){
    x.32[i,]<-ay[(P11 - lagP3[i]*s + 1):(n - lagP3[i]*s)]
  }
  x.3[seq(s,P3*s,s),]<-x.32
  for (i in 1:P3){
    for (j in 1:p3){
      x.33[[i]][j,]<-ay[(P11 - (lagp3[j]+s*lagP3[i]) + 1):(n -(lagp3[j]+s*lagP3[i]))]
    }
  }
  for (i in 1:P3){ 
    x.3[seq(i*s+1,i*s+p3,1),]<-x.33[[i]]
  }
  for (i in 1:q3) {
    x.34[i, ] <- thresVar[(P11 - lagq3[i] + 1):(n - lagq3[i])]
  }
  x.3[(p3+s*P3+1):(p3+s*P3+q3),]<-x.34
  if (constant == 1) {
    tx.3 <- cbind(1, t(x.3[ ,lag.y>thres.2]))
  }
  else  {
    tx.3 <- t(x.3[ ,lag.y>thres.2])
  }
  
  ln.li <-  -(((n-P11)*log(2*pi))/2)-((t(y.1 - tx.1 %*% p.1) %*% (y.1 - tx.1 %*% p.1))/(2 *sig.1)) - ((t(y.2 - tx.2 %*% p.2) %*% (y.2 - tx.2 %*% p.2))/(2 * sig.2)) - ((t(y.3 - tx.3 %*% p.3) %*% (y.3 - tx.3 %*% p.3))/(2 *sig.3))-((n1/2) * log(sig.1)) - ((n2/2) * log(sig.2))- ((n3/2) * log(sig.3))
  
  return(ln.li)
}


##################################################################################
##############################################################

###################### Extrae el valor umbral        
#####################################     tar3e.thresxG        Metropolis-Hasting, con densidad instrumental GAUSSIANA , caso tres reg?menes

tar3e.thresxG=function(ay, p1, p2, p3, P1, P2, P3, q1, q2, q3,  ph.1, PH.1, qh.1, ph.2, PH.2, qh.2, ph.3, PH.3, qh.3, sig.1, sig.2,  sig.3, lagd, thres.1, thres.2, step.r, h, bound, lagp1, lagp2, lagp3, lagP1, lagP2, lagP3, lagq1, lagq2, lagq3,  constant,  thresVar, s) 
{
  P11 <- max(max(lagp1)+s*max(lagP1), max(lagp2)+s*max(lagP2), max(lagp3)+s*max(lagP3), max(lagq1), max(lagq2), max(lagq3)) 
  n <- length(ay)
  lag.y <- thresVar[(P11 + 1 - lagd):(n - lagd)]
  
  
  new.r1 <- thres.1 + step.r*rnorm(1, mean = 0, sd = 1)
  new.r2 <- thres.2 + step.r*rnorm(1, mean = 0, sd = 1)
  new.r<-c(new.r1,new.r2)
  
  m1<-sum(lag.y<=new.r1)
  m2<-sum(lag.y>new.r1 & lag.y<=new.r2)
  m3<-sum(lag.y>new.r2)
  m<-c(m1,m2,m3)
  
  repeat {
    if ( any(new.r < bound[1]) | any(new.r > bound[2]) | any(m<n/h) | any(m>=n) | (new.r1>=new.r2)) 
    {
      new.r1 <- thres.1 + step.r*rnorm(1, mean = 0, sd = 1)
      new.r2 <- thres.2 + step.r*rnorm(1, mean = 0, sd = 1)
      new.r<-c(new.r1,new.r2)
      
      m1<-sum(lag.y<=new.r1)
      m2<-sum(lag.y>new.r1 & lag.y<=new.r2)
      m3<-sum(lag.y>new.r2)
      m<-c(m1,m2,m3)
      
    }
    else    break
  }
  
  old.lik <- tar3e.likx(ay, p1, p2, p3, P1, P2, P3, q1, q2, q3, ph.1, PH.1, qh.1, ph.2, PH.2, qh.2, ph.3, PH.3, qh.3, sig.1, sig.2, sig.3, lagd, thres.1, thres.2, lagp1, lagp2, lagp3, lagP1, lagP2, lagP3, lagq1, lagq2, lagq3,  constant, thresVar, s)
  new.lik <- tar3e.likx(ay, p1, p2, p3, P1, P2, P3, q1, q2, q3, ph.1, PH.1, qh.1, ph.2, PH.2, qh.2, ph.3, PH.3, qh.3, sig.1, sig.2, sig.3, lagd,  new.r1,  new.r2, lagp1, lagp2, lagp3, lagP1, lagP2, lagP3, lagq1, lagq2, lagq3,  constant, thresVar, s)
  
  
  if ((new.lik - old.lik) > log(runif(1))) {
    r.count = 1
  }
  else {
    new.r1 <- thres.1
    new.r2 <- thres.2
    r.count <- 0
  }
  umbral<-list(r.count=r.count, new.r1=new.r1, new.r2=new.r2)
  return(umbral)
  
}

################################################################################################
########################################################################


#############  Identificación del rezago  d       
#####################    tar3e.lagdx


tar3e.lagdx=function(ay, p1, p2, p3, P1, P2, P3, q1, q2, q3, ph.1, PH.1, qh.1, ph.2, PH.2, qh.2, ph.3, PH.3, qh.3, sig.1, sig.2, sig.3,  thres.1, thres.2, lagp1, lagp2, lagp3, lagP1, lagP2, lagP3, lagq1, lagq2, lagq3, constant, d0, thresVar, s) 
{
  loglik <- lik <- NULL
  
  for (i in 1:(d0+1)) {
    
    loglik[i] <- tar3e.likx(ay, p1, p2, p3, P1, P2, P3, q1, q2, q3, ph.1, PH.1, qh.1, ph.2, PH.2, qh.2, ph.3, PH.3, qh.3, sig.1, sig.2, sig.3, (i-1), thres.1, thres.2, lagp1, lagp2, lagp3, lagP1, lagP2, lagP3, lagq1, lagq2, lagq3,  constant, thresVar, s)
    
  }
  lik <- exp(loglik - max(loglik))
  lagd <- (sum((cumsum(lik)/sum(lik)) < runif(1, min = 0, max = 1)))
  return(lagd)
}


###################################################################################
#####################################################



######################## cálculo de estadísticas resumen       
###############################################################  tar3e.summaryx
#####  x es par.set del programa principal


tar3e.summaryx=function(x, lagp1, lagp2, lagp3, lagP1, lagP2, lagP3,  lagq1, lagq2, lagq3,  constant) 
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
      rownames(temp) <- c(paste("phi1", c(0, lagp1), sep = "."), paste("PHI1", lagP1, sep = "."), paste("qhi1", lagq1, sep = "."),paste("phi2", c(0, lagp2), sep = "."),paste("PHI2", lagP2, sep = "."), paste("qhi2", lagq2, sep = "."), paste("phi3", c(0, lagp3), sep = "."), paste("PHI3", lagP3, sep = "."), paste("qhi3", lagq3, sep = "."), "sigma^2 1", "sigma^2 2", "sigma^2 3", "r1", "r2")
    }
    if(constant==0) {
      rownames(temp) <- c(paste("phi1", lagp1, sep = "."), paste("PHI1", lagP1, sep = "."), paste("qhi1", lagq1, sep = "."),paste("phi2", lagp2, sep = "."),paste("PHI2", lagP2, sep = "."), paste("qhi2", lagq2, sep = "."), paste("phi3", lagp3, sep = "."), paste("PHI3", lagP3, sep = "."), paste("qhi3", lagq3, sep = "."), "sigma^2 1", "sigma^2 2", "sigma^2 3", "r1", "r2")
    }
    
  }
  return(temp)
}


###################################################################
####################################



########################################        programa principal    Estimaci?n Bayesiana, residuales   
##############################################       BAYES3E.TARX


BAYES3E.TARX=function(x, lagp1, lagp2, lagp3, lagP1, lagP2, lagP3,  lagq1, lagq2, lagq3, Iteration, Burnin, constant, step.thv, h, thresVar, s, d0)
  
{
  refresh<-1000
  
  p1 <- length(lagp1)
  p2 <- length(lagp2)
  p3 <- length(lagp3)
  
  P1 <- length(lagP1)
  P2 <- length(lagP2)
  P3 <- length(lagP3)
  
  q1 <- length(lagq1)
  q2 <- length(lagq2)
  q3 <- length(lagq3)
  
  nx <- length(x)
  
  
  ########## condiciones iniciales #################
  
  phi.1=rep(0.05,p1+constant)
  phi.2=rep(0.05,p2+constant)
  phi.3=rep(0.05,p3+constant)
  
  
  PHI.1=rep(0.05,P1)
  PHI.2=rep(0.05,P2)
  PHI.3=rep(0.05,P3)
  
  qhi.1=rep(0.05,q1)
  qhi.2=rep(0.05,q2)
  qhi.3=rep(0.05,q3)
  
  sigma.1=0.20
  sigma.2=0.20
  sigma.3=0.20
  
  thres.1=quantile(thresVar,probs=c(0.25))
  thres.2=quantile(thresVar,probs=c(0.75))
  lagd=3
  
  accept.r=0
  sum.r=0
  
  ############# hiperparámetros ##############
  
  mu0ph1=matrix(0,nrow=p1+constant,ncol=1)
  v0ph1=diag(0.1,p1+constant)
  
  mu0ph2=matrix(0,nrow=p2+constant,ncol=1)
  v0ph2=diag(0.1,p2+constant)
  
  mu0ph3=matrix(0,nrow=p3+constant,ncol=1)
  v0ph3=diag(0.1,p3+constant)
  
  mu0PH1=matrix(0,nrow=P1,ncol=1)
  v0PH1=diag(0.1,P1)
  
  mu0PH2=matrix(0,nrow=P2,ncol=1)
  v0PH2=diag(0.1,P2)
  
  mu0PH3=matrix(0,nrow=P3,ncol=1)
  v0PH3=diag(0.1,P3)
  
  mu0qh1=matrix(0,nrow=q1,ncol=1)
  v0qh1=diag(0.1,q1)
  
  mu0qh2=matrix(0,nrow=q2,ncol=1)
  v0qh2=diag(0.1,q2)
  
  mu0qh3=matrix(0,nrow=q3,ncol=1)
  v0qh3=diag(0.1,q3)
  
  v0=3
  lambda0=var(x)/3
  bound.thv=c(min(thresVar),max(thresVar))
  
  
  ####################################################################
  
  par.set <- matrix(NA, nrow = Iteration, ncol = (length(c(phi.1, PHI.1, qhi.1, phi.2, PHI.2, qhi.2,  phi.3, PHI.3, qhi.3, sigma.1, sigma.2,  sigma.3, thres.1, thres.2, lagd))))
  loglik.1 <- loglik.2 <- DIC <-lnaprioris<-logvermarg<-NA
  
  for (igb in 1:Iteration) {
    
    phi.1 <- tar3e.coeffxph(1, x, p1, P1, q1, sigma.1, lagd, thres.1, thres.2, mu0ph1, v0ph1, PHI.1, qhi.1, lagp1, lagp2, lagp3, lagP1, lagP2, lagP3, lagq1, lagq2, lagq3, constant, thresVar, s)
    phi.2 <- tar3e.coeffxph(2, x, p2, P2, q2, sigma.2, lagd, thres.1, thres.2, mu0ph2, v0ph2, PHI.2, qhi.2, lagp1, lagp2, lagp3, lagP1, lagP2, lagP3, lagq1, lagq2, lagq3, constant, thresVar, s)
    phi.3 <- tar3e.coeffxph(3, x, p3, P3, q3, sigma.3, lagd, thres.1, thres.2, mu0ph3, v0ph3, PHI.3, qhi.3, lagp1, lagp2, lagp3, lagP1, lagP2, lagP3, lagq1, lagq2, lagq3, constant, thresVar, s)
    PHI.1 <- tar3e.coeffxPH(1, x, p1, P1, q1, sigma.1, lagd, thres.1, thres.2, mu0PH1, v0PH1, phi.1, qhi.1, lagp1, lagp2, lagp3, lagP1, lagP2, lagP3, lagq1, lagq2, lagq3, constant, thresVar, s)           
    PHI.2 <- tar3e.coeffxPH(2, x, p2, P2, q2, sigma.2, lagd, thres.1, thres.2, mu0PH2, v0PH2, phi.2, qhi.2, lagp1, lagp2, lagp3, lagP1, lagP2, lagP3, lagq1, lagq2, lagq3, constant, thresVar, s)
    PHI.3 <- tar3e.coeffxPH(3, x, p3, P3, q3, sigma.3, lagd, thres.1, thres.2, mu0PH3, v0PH3, phi.3, qhi.3, lagp1, lagp2, lagp3, lagP1, lagP2, lagP3, lagq1, lagq2, lagq3, constant, thresVar, s)
    qhi.1 <- tar3e.coeffxqh(1, x, p1, P1, q1, sigma.1, lagd, thres.1, thres.2, mu0qh1, v0qh1, phi.1, PHI.1, lagp1, lagp2, lagp3, lagP1, lagP2, lagP3, lagq1, lagq2, lagq3, constant, thresVar, s) 
    qhi.2 <- tar3e.coeffxqh(2, x, p2, P2, q2, sigma.2, lagd, thres.1, thres.2, mu0qh2, v0qh2, phi.2, PHI.2, lagp1, lagp2, lagp3, lagP1, lagP2, lagP3, lagq1, lagq2, lagq3, constant, thresVar, s) 
    qhi.3 <- tar3e.coeffxqh(3, x, p3, P3, q3, sigma.3, lagd, thres.1, thres.2, mu0qh3, v0qh3, phi.3, PHI.3, lagp1, lagp2, lagp3, lagP1, lagP2, lagP3, lagq1, lagq2, lagq3, constant, thresVar, s)            
    sigma.1 <- tar3e.sigmax(1, x, thres.1, thres.2,  lagd, p1, P1, q1, phi.1, PHI.1, qhi.1, v0, lambda0, lagp1, lagp2, lagp3, lagP1, lagP2, lagP3, lagq1, lagq2, lagq3, constant, thresVar, s)          
    sigma.2 <- tar3e.sigmax(2, x, thres.1, thres.2,  lagd, p2, P2, q2, phi.2, PHI.2, qhi.2, v0, lambda0, lagp1, lagp2, lagp3, lagP1, lagP2, lagP3, lagq1, lagq2, lagq3, constant, thresVar, s)          
    sigma.3 <- tar3e.sigmax(3, x, thres.1, thres.2,  lagd, p3, P3, q3, phi.3, PHI.3, qhi.3, v0, lambda0, lagp1, lagp2, lagp3, lagP1, lagP2, lagP3, lagq1, lagq2, lagq3, constant, thresVar, s)          
    lagd <-tar3e.lagdx(x, p1, p2, p3, P1, P2, P3, q1, q2, q3, phi.1, PHI.1, qhi.1, phi.2, PHI.2, qhi.2, phi.3, PHI.3, qhi.3, sigma.1, sigma.2, sigma.3,  thres.1, thres.2, lagp1, lagp2, lagp3, lagP1, lagP2, lagP3, lagq1, lagq2, lagq3, constant, d0, thresVar, s)
    thresholdt<-tar3e.thresxG(x, p1, p2, p3, P1, P2, P3, q1, q2, q3, phi.1, PHI.1, qhi.1, phi.2, PHI.2, qhi.2, phi.3, PHI.3, qhi.3, sigma.1, sigma.2,  sigma.3, lagd, thres.1, thres.2, step.thv, h, bound.thv, lagp1, lagp2, lagp3, lagP1, lagP2, lagP3, lagq1, lagq2, lagq3,  constant,  thresVar, s)           
    
    
    sum.r <- sum.r + thresholdt$r.count
    thres.1 <- thresholdt$new.r1
    thres.2 <- thresholdt$new.r2
    
    
    par.set[igb, ] <- c(phi.1, PHI.1, qhi.1, phi.2, PHI.2, qhi.2, phi.3, PHI.3, qhi.3, sigma.1, sigma.2, sigma.3, thres.1, thres.2, lagd)
    
    loglik.1[igb] <- tar3e.likx(x, p1, p2, p3, P1, P2, P3, q1, q2, q3, phi.1, PHI.1, qhi.1, phi.2, PHI.2, qhi.2, phi.3, PHI.3, qhi.3, sigma.1, sigma.2, sigma.3, lagd, thres.1, thres.2, lagp1, lagp2, lagp3, lagP1, lagP2, lagP3, lagq1, lagq2, lagq3,  constant, thresVar, s)    
    
    lnaprioris[igb]<- -0.5*((p1+constant)*log(2*pi)+(p1+constant)*log(det(solve(v0ph1)))+phi.1%*%v0ph1%*%t(phi.1))-0.5*((p2+constant)*log(2*pi)+(p2+constant)*log(det(solve(v0ph2)))+phi.2%*%v0ph2%*%t(phi.2))-0.5*((p3+constant)*log(2*pi)+(p3+constant)*log(det(solve(v0ph3)))+phi.3%*%v0ph3%*%t(phi.3))-0.5*(P1*log(2*pi)+P1*log(det(solve(v0PH1)))+PHI.1%*%v0PH1%*%t(PHI.1))-0.5*(P2*log(2*pi)+P2*log(det(solve(v0PH2)))+PHI.2%*%v0PH2%*%t(PHI.2))-0.5*(P3*log(2*pi)+P3*log(det(solve(v0PH3)))+PHI.3%*%v0PH3%*%t(PHI.3))-0.5*(q1*log(2*pi)+q1*log(det(solve(v0qh1)))+qhi.1%*%v0qh1%*%t(qhi.1))-0.5*(q2*log(2*pi)+q2*log(det(solve(v0qh2)))+qhi.2%*%v0qh2%*%t(qhi.2))-0.5*(q3*log(2*pi)+q3*log(det(solve(v0qh3)))+qhi.3%*%v0qh3%*%t(qhi.3))+(1.5*log(var(x)/2)-log(gamma(1.5))-2.5*log(sigma.1)-0.5*var(x)*(1/sigma.1))+(1.5*log(var(x)/2)-log(gamma(1.5))-2.5*log(sigma.2)-0.5*var(x)*(1/sigma.2))+(1.5*log(var(x)/2)-log(gamma(1.5))-2.5*log(sigma.3)-0.5*var(x)*(1/sigma.3))+log(prod(seq(1,2,1))/(bound.thv[2]-bound.thv[1])^2)+log(1/(d0+1))
    
    logvermarg[igb]<-loglik.1[igb]+lnaprioris[igb]
    
    
    ncol0 <- ncol(par.set)
    
    if (igb%%refresh == 0) 
    {
      cat("iteration = ", igb, "\n")
      cat("regime 1 = ", round(phi.1, 4), "\n")
      cat("regime 2 = ", round(phi.2, 4), "\n")
      cat("regime 3 = ", round(phi.3, 4), "\n")
      cat("regime 1 = ", round(PHI.1, 4), "\n")
      cat("regime 2 = ", round(PHI.2, 4), "\n")
      cat("regime 3= ", round(PHI.3, 4), "\n")
      cat("regime 1 = ", round(qhi.1, 4), "\n")
      cat("regime 2 = ", round(qhi.2, 4), "\n")
      cat("regime 3 = ", round(qhi.3, 4), "\n")
      cat("sigma^2 1  = ", round(sigma.1, 4), "\n")
      cat("sigma^2 2  = ", round(sigma.2, 4), "\n")
      cat("sigma^2 3  = ", round(sigma.3, 4), "\n")
      cat("r1        = ", round(thres.1, 4), "\n")
      cat("r2        = ", round(thres.2, 4), "\n")
      
      accept.r <- (sum.r/igb) * 100
      cat("Tasa de aceptación de r = ", round(accept.r, 4), "%", "\n")
      lag.freq <- rep(0, (d0+1))
      for (i in 1:(d0+1)) {
        lag.freq[i] <- sum(par.set[1:igb, ncol0] == (i-1))
      }
      lag.freq <- t(matrix(lag.freq, dimnames = list(c(as.character(0:d0)), c("Frec."))))
      cat("Escogencia del Rezago : ", "\n")
      print(lag.freq)
      cat("------------", "\n")
    }
  }      ### fin del igb
  
  mcmc.stat <-tar3e.summaryx(par.set[(Burnin + 1):Iteration, 1:(ncol0 - 1)], lagp1, lagp2, lagp3, lagP1, lagP2, lagP3,  lagq1, lagq2, lagq3,  constant) 
  print(round(mcmc.stat, 4))
  
  lag.y <- c(0:d0)
  lag.d <- lag.y[lag.freq == max(lag.freq)]
  cat("Escogencia del Rezago : ", "\n")
  print(lag.freq)
  cat("------------", "\n")
  cat("La probabilidad a posterior m?s alta corresponde al rezago: ", lag.d, "\n")
  
  loglik.2<- tar3e.likx(x, p1, p2, p3, P1, P2, P3, q1, q2, q3, mcmc.stat[1:(p1+ constant), 1] , mcmc.stat[(p1+constant+1):(p1+constant+P1), 1],mcmc.stat[(p1+constant+P1+1):(p1+constant+P1+q1), 1] ,mcmc.stat[(p1+constant+P1+q1+1):(p1+constant+P1+q1+p2+constant), 1], mcmc.stat[(p1+constant+P1+q1+p2+constant+1):(p1+constant+P1+q1+p2+constant+P2), 1], mcmc.stat[(p1+constant+P1+q1+p2+constant+P2+1):(p1+constant+P1+q1+p2+constant+P2+q2), 1],mcmc.stat[(p1+constant+P1+q1+p2+constant+P2+q2+1):(p1+constant+P1+q1+p2+constant+P2+q2+p3+constant), 1] ,mcmc.stat[(p1+constant+P1+q1+p2+constant+P2+q2+p3+constant+1):(p1+constant+P1+q1+p2+constant+P2+q2+p3+constant+P3), 1] , mcmc.stat[(p1+constant+P1+q1+p2+constant+P2+q2+p3+constant+P3+1):(p1+constant+P1+q1+p2+constant+P2+q2+p3+constant+P3+q3), 1], mcmc.stat[p1+constant+P1+q1+p2+constant+P2+q2+p3+constant+P3+q3+1, 1],mcmc.stat[p1+constant+P1+q1+p2+constant+P2+q2+p3+constant+P3+q3+2, 1] ,mcmc.stat[p1+constant+P1+q1+p2+constant+P2+q2+p3+constant+P3+q3+3, 1], lag.d, mcmc.stat[p1+constant+P1+q1+p2+constant+P2+q2+p3+constant+P3+q3+4, 1],mcmc.stat[p1+constant+P1+q1+p2+constant+P2+q2+p3+constant+P3+q3+5, 1], lagp1, lagp2, lagp3, lagP1, lagP2, lagP3, lagq1, lagq2, lagq3,  constant, thresVar, s)     
  
  DIC<- (2*(-2*sum(loglik.1[(Burnin + 1):Iteration]))/length(loglik.1[(Burnin + 1):Iteration])) - (-2*loglik.2)
  cat(" DIC = ", DIC, "\n")
  
  #lnapriorisfijo<-NA
  #lnapriorisfijo<- -0.5*((p1+constant)*log(2*pi)+(p1+constant)*log(det(solve(v0ph1)))+ t(mcmc.stat[1:(p1 + constant), 1])%*%v0ph1%*%( mcmc.stat[1:(p1  + constant), 1]))-0.5*(P1*log(2*pi)+P1*log(det(solve(v0PH1)))+ t(mcmc.stat[(p1+constant+1):(p1+constant+P1), 1])%*%v0PH1%*%(mcmc.stat[(p1+constant+1):(p1+constant+P1), 1]))-0.5*(q1*log(2*pi)+q1*log(det(solve(v0qh1)))+ t(mcmc.stat[(p1+constant+P1+1):(p1+constant+P1+q1), 1])%*%v0qh1%*%(mcmc.stat[(p1+constant+P1+1):(p1+constant+P1+q1), 1]))-0.5*((p2+constant)*log(2*pi)+(p2+constant)*log(det(solve(v0ph2)))+ t(mcmc.stat[(p1+constant+P1+q1+1):(p1+constant+P1+q1+p2+constant), 1])%*%v0ph2%*%(mcmc.stat[(p1+constant+P1+q1+1):(p1+constant+P1+q1+p2+constant), 1]))-0.5*(P2*log(2*pi)+P2*log(det(solve(v0PH2)))+ t(mcmc.stat[(p1+constant+P1+q1+p2+constant+1):(p1+constant+P1+q1+p2+constant+P2), 1])%*%v0PH2%*%(mcmc.stat[(p1+constant+P1+q1+p2+constant+1):(p1+constant+P1+q1+p2+constant+P2), 1]))-0.5*(q2*log(2*pi)+q2*log(det(solve(v0qh2)))+ t(mcmc.stat[(p1+constant+P1+q1+p2+constant+P2+1):(p1+constant+P1+q1+p2+constant+P2+q2), 1])%*%v0qh2%*%(mcmc.stat[(p1+constant+P1+q1+p2+constant+P2+1):(p1+constant+P1+q1+p2+constant+P2+q2), 1]))-0.5*((p3+constant)*log(2*pi)+(p3+constant)*log(det(solve(v0ph3)))+ t(mcmc.stat[(p1+constant+P1+q1+p2+constant+P2+q2+1):(p1+constant+P1+q1+p2+constant+P2+q2+p3+constant), 1])%*%v0ph3%*%(mcmc.stat[(p1+constant+P1+q1+p2+constant+P2+q2+1):(p1+constant+P1+q1+p2+constant+P2+q2+p3+constant), 1]))-0.5*(P3*log(2*pi)+P3*log(det(solve(v0PH3)))+ t(mcmc.stat[(p1+constant+P1+q1+p2+constant+P2+q2+p3+constant+1):(p1+constant+P1+q1+p2+constant+P2+q2+p3+constant+P3), 1])%*%v0PH3%*%(mcmc.stat[(p1+constant+P1+q1+p2+constant+P2+q2+p3+constant+1):(p1+constant+P1+q1+p2+constant+P2+q2+p3+constant+P3), 1]))-0.5*(q3*log(2*pi)+q3*log(det(solve(v0qh3)))+ t(mcmc.stat[(p1+constant+P1+q1+p2+constant+P2+q2+p3+constant+P3+1):(p1+constant+P1+q1+p2+constant+P2+q2+p3+constant+P3+q3), 1])%*%v0qh3%*%(mcmc.stat[(p1+constant+P1+q1+p2+constant+P2+q2+p3+constant+P3+1):(p1+constant+P1+q1+p2+constant+P2+q2+p3+constant+P3+q3), 1]))+(1.5*log(var(x)/2)-log(gamma(1.5))-2.5*log(mcmc.stat[(p1+constant+P1+q1+p2+constant+P2+q2+p3+constant+P3+q3+1), 1]), 1])-0.5*var(x)*(1/mcmc.stat[(p1+constant+P1+q1+p2+constant+P2+q2+p3+constant+P3+q3+1), 1]), 1]))+(1.5*log(var(x)/2)-log(gamma(1.5))-2.5*log(mcmc.stat[(p1+constant+P1+q1+p2+constant+P2+q2+p3+constant+P3+q3+2), 1]), 1])-0.5*var(x)*(1/mcmc.stat[(p1+constant+P1+q1+p2+constant+P2+q2+p3+constant+P3+q3+2), 1]), 1]))+(1.5*log(var(x)/2)-log(gamma(1.5))-2.5*log(mcmc.stat[(p1+constant+P1+q1+p2+constant+P2+q2+p3+constant+P3+q3+3), 1]), 1])-0.5*var(x)*(1/mcmc.stat[(p1+constant+P1+q1+p2+constant+P2+q2+p3+constant+P3+q3+3), 1]), 1]))+log(prod(seq(1,2,1))/(bound.thv[2]-bound.thv[1])^2)+log(1/(d0+1))
  
  
  if (constant==1) 
  {       
    con.1 <- mcmc.stat[1, 1]
    parp.1 <- mcmc.stat[2:(p1+ constant), 1]
    parP.1 <- mcmc.stat[(p1+constant+1):(p1+constant+P1), 1]
    parq.1 <- mcmc.stat[(p1+constant+P1+1):(p1+constant+P1+q1), 1]
    
    con.2 <- mcmc.stat[p1+constant+P1+q1+1, 1]
    parp.2 <- mcmc.stat[(p1+constant+P1+q1+1+1):(p1+constant+P1+q1+p2+constant), 1]
    parP.2 <- mcmc.stat[(p1+constant+P1+q1+p2+constant+1):(p1+constant+P1+q1+p2+constant+P2), 1]
    parq.2 <- mcmc.stat[(p1+constant+P1+q1+p2+constant+P2+1):(p1+constant+P1+q1+p2+constant+P2+q2), 1]
    
    con.3 <- mcmc.stat[p1+constant+P1+q1+p2+constant+P2+q2+1, 1]
    parp.3 <- mcmc.stat[(p1+constant+P1+q1+p2+constant+P2+q2+1+1):(p1+constant+P1+q1+p2+constant+P2+q2+p3+constant), 1]
    parP.3 <- mcmc.stat[(p1+constant+P1+q1+p2+constant+P2+q2+p3+constant+1):(p1+constant+P1+q1+p2+constant+P2+q2+p3+constant+P3), 1]
    parq.3 <- mcmc.stat[(p1+constant+P1+q1+p2+constant+P2+q2+p3+constant+P3+1):(p1+constant+P1+q1+p2+constant+P2+q2+p3+constant+P3+q3), 1]
    
    
    sig.1u <- mcmc.stat[p1+constant+P1+q1+p2+constant+P2+q2+p3+constant+P3+q3+1,1]
    sig.2d <- mcmc.stat[p1+constant+P1+q1+p2+constant+P2+q2+p3+constant+P3+q3+2,1]
    sig.3t <- mcmc.stat[p1+constant+P1+q1+p2+constant+P2+q2+p3+constant+P3+q3+3,1]
    
    
    thv.1   <-  mcmc.stat[p1+constant+P1+q1+p2+constant+P2+q2+p3+constant+P3+q3+4, 1]
    thv.2   <-  mcmc.stat[p1+constant+P1+q1+p2+constant+P2+q2+p3+constant+P3+q3+5, 1]
  }
  
  
  if (constant== 0) 
  {       
    con.1 <- 0
    parp.1 <- mcmc.stat[1:p1, 1]
    parP.1 <- mcmc.stat[(p1+1):(p1+P1), 1]
    parq.1 <- mcmc.stat[(p1+P1+1):(p1+P1+q1), 1]
    
    con.2 <- 0
    parp.2 <- mcmc.stat[(p1+P1+q1+1):(p1+P1+q1+p2), 1]
    parP.2 <- mcmc.stat[(p1+P1+q1+p2+1):(p1+P1+q1+p2+P2), 1]
    parq.2 <- mcmc.stat[(p1+P1+q1+p2+P2+1):(p1+P1+q1+p2+P2+q2), 1]
    
    con.3 <- 0
    parp.3 <- mcmc.stat[(p1+P1+q1+p2+P2+q2+1):(p1+P1+q1+p2+P2+q2+p3), 1]
    parP.3 <- mcmc.stat[(p1+P1+q1+p2+P2+q2+p3+1):(p1+P1+q1+p2+P2+q2+p3+P3), 1]
    parq.3 <- mcmc.stat[(p1+P1+q1+p2+P2+q2+p3+P3+1):(p1+P1+q1+p2+P2+q2+p3+P3+q3), 1]
    
    sig.1u <- mcmc.stat[p1+P1+q1+p2+P2+q2+p3+P3+q3+1,1]
    sig.2d <- mcmc.stat[p1+P1+q1+p2+P2+q2+p3+P3+q3+2,1]
    sig.3t <- mcmc.stat[p1+P1+q1+p2+P2+q2+p3+P3+q3+3,1]
    
    thv.1  <- mcmc.stat[p1+P1+q1+p2+P2+q2+p3+P3+q3+4, 1]
    thv.2  <- mcmc.stat[p1+P1+q1+p2+P2+q2+p3+P3+q3+5, 1]
  }
  
  
  
  
  maxd <- max(max(lagp1)+s*max(lagP1), max(lagp2)+s*max(lagP2), max(lagp3)+s*max(lagP3), max(lagq1), max(lagq2), max(lagq3))
  
  
  residual <-residual.est<- rep(0, (nx - maxd))
  residual1<-residual2<-residual3<-rep(0, (nx - maxd))
  
  multipP1<-matrix(NA,nrow=(nx-maxd), ncol=p1*P1)
  multipP2<-matrix(NA,nrow=(nx-maxd), ncol=p2*P2)
  multipP3<-matrix(NA,nrow=(nx-maxd), ncol=p3*P3)
  
  
  for (t in (maxd + 1):nx) {
    
    if (thresVar[t - lag.d] <= thv.1)  {
      
      for (i in 1:P1){
        for (j in 1:p1){
          multipP1[t-maxd, (i*j+(p1-j)*(i-1))]<-parP.1[i]*parp.1[j]*x[t-(lagp1[j]+s*lagP1[i])]
        }
      }
      
      residual[t - maxd] <- (x[t] - sum(con.1, parp.1[1:p1]*x[t - lagp1], parP.1[1:P1]*x[t - s*lagP1], -multipP1[t-maxd, ],  parq.1[1:q1]*thresVar[t - lagq1]))
      residual.est[t - maxd]<-residual[t - maxd]/sqrt(sig.1u)
      residual1[t - maxd] <- (x[t] - sum(con.1, parp.1[1:p1]*x[t - lagp1], parP.1[1:P1]*x[t - s*lagP1], - multipP1[t-maxd, ],  parq.1[1:q1]*thresVar[t - lagq1]))
    }
    
    if (thresVar[t - lag.d]>thv.1 & thresVar[t - lag.d]<=thv.2){
      
      for (i in 1:P2){
        for (j in 1:p2){
          multipP2[t-maxd, (i*j+(p2-j)*(i-1))]<-parP.2[i]*parp.2[j]*x[t-(lagp2[j]+s*lagP2[i])]
        }
      }
      
      residual[t - maxd] <- (x[t] - sum(con.2, parp.2[1:p2]*x[t - lagp2], parP.2[1:P2]*x[t - s*lagP2],  -multipP2[t-maxd, ],  parq.2[1:q2]*thresVar[t - lagq2]))
      residual.est[t - maxd]<-residual[t - maxd]/sqrt(sig.2d)
      residual2[t - maxd] <- (x[t] - sum(con.2, parp.2[1:p2]*x[t - lagp2], parP.2[1:P2]*x[t - s*lagP2], -multipP2[t-maxd, ],  parq.2[1:q2]*thresVar[t - lagq2]))
    }
    
    if (thresVar[t - lag.d]>thv.2){
      
      for (i in 1:P3){
        for (j in 1:p3){
          multipP3[t-maxd, (i*j+(p3-j)*(i-1))]<-parP.3[i]*parp.3[j]*x[t-(lagp3[j]+s*lagP3[i])]
        }
      }
      
      residual[t - maxd] <- (x[t] - sum(con.3, parp.3[1:p3]*x[t - lagp3], parP.3[1:P3]*x[t - s*lagP3],  -multipP3[t-maxd, ],  parq.3[1:q3]*thresVar[t - lagq3]))
      residual.est[t - maxd]<-residual[t - maxd]/sqrt(sig.3t)
      residual3[t - maxd] <- (x[t] - sum(con.3, parp.3[1:p3]*x[t - lagp3], parP.3[1:P3]*x[t - s*lagP3], -multipP3[t-maxd, ],  parq.3[1:q3]*thresVar[t - lagq3]))
    }
    
    
  }
  
  
  res1<-sum(residual1^2)
  res2<-sum(residual2^2)
  res3<-sum(residual3^2)
  
  lag.yy<-thresVar[(maxd+1-lag.d):(nx-lag.d)]
  n1<-sum(lag.yy<=thv.1) 
  n2<-sum(lag.yy>thv.1 &  lag.yy<=thv.2)
  n3<-sum(lag.yy>thv.2)
  
  NAIC<-NA
  NAIC<-((n1*log(res1/n1)+2*(p1+constant+P1+q1)) + (n2*log(res2/n2)+2*(p2+constant+P2+q2)) + (n3*log(res3/n3)+2*(p3+constant+P3+q3)))/(n1+n2+n3)
  cat("NAIC", NAIC,"\n")
  
  
  
  
  tar <- list(mcmc = par.set, posterior = par.set[(Burnin + 1):Iteration, 1:ncol0], coef.par = round(mcmc.stat, 4),   residual = residual, residual.est=residual.est, lagd = lag.d, DIC = DIC, NAIC=NAIC, logverosimil=loglik.1[(Burnin+1):Iteration], log.ver=logvermarg[(Burnin+1):Iteration])
  
  return(tar)
  
}


######################## CARGUE DE BASES DE DATOS
setwd("D:/sarbelaez/Documents/Maestría/Tesis/Bases de datos/Reino Unido/")
Base=fread("Desempleo_uk.csv",sep=",")
Datos=ts(Base[1:132,2],start=c(1983,2),freq=4)
Xt=diff((Datos))
pib=fread("PIB_uk.csv",sep=",")
Zt=ts(pib[34:166,2],start = c(1983,2),freq=4)
Zt=diff(log(Zt))*100

####################################### METODO DE CONGDON
set.seed(525)
repeticiones<-1     #### número de repeticiones

Iteration<-12000
Burnin<-4000

regimenes<-3  ######  máximo número de regímenes considerado

x<-Xt
thresVar<-Zt
#### Fijar p, P, q y d máximos (depende de prueba de Tsay)
set.seed(525)
lagp1.1<-1:2
lagP1.1<-1:2
lagq1.1<-1

lagp1.2<-1:2
lagP1.2<-1:2
lagq1.2<-1
lagp2.2<-1:2
lagP2.2<-1:2
lagq2.2<-1

lagp1.3<-1:2
lagP1.3<-1:2
lagq1.3<-1
lagp2.3<-1:2
lagP2.3<-1:2
lagq2.3<-1
lagp3.3<-1:2
lagP3.3<-1:2
lagq3.3<-1
constant=1
h=25
s=4
step.thv=0.04 #se ajusta el tamaño del paso de acuerdo con la tasa de aceptación
d0=3


########################

probapost<-matrix(NA, nrow=repeticiones, ncol=regimenes)
A<-matrix(NA, nrow=repeticiones, ncol=regimenes)
B<-matrix(NA, nrow=repeticiones, ncol=regimenes)

criterioDIC<-matrix(NA, nrow=repeticiones, ncol=1)
criterioNAIC<-matrix(NA, nrow=repeticiones, ncol=1)
criterioCONGDON<-matrix(NA, nrow=repeticiones, ncol=1)

metodoCong<-matrix(NA, nrow=repeticiones, ncol=1)
metodoDIC<-matrix(NA, nrow=repeticiones, ncol=1)
metodoNAIC<-matrix(NA, nrow=repeticiones, ncol=1)

for (k in 1:repeticiones)
{
  
  cat("---------------", "\n")
  cat("iteración = ", k, "\n")
  cat("---------------", "\n")
  
  #z<-ar.simu(nob, p, ph,  sig,  lagp)    ### se cambia por un SAR
  ## z=sar.simu=function(nob, p, P, ph, PH,  sig, lagp, lagP, s) 
  #thres=median(z)    
  ###  se cambia por thres.1=quantile(z,0.25) y thres.2=quantile(z,0.75)  ,  cuando se trabaje con 3 regimenes
  #xx<-tsar2.simux(nob, p1, p2, P1, P2, q1, q2, ph.1, ph.2, PH.1, PH.2, qh.1, qh.2,  sig.1, sig.2, lagd, thres=thres, lagp1, lagp2, lagP1, lagP2, lagq1, lagq2, z, s) 
  ####   xx se puede cambiar por el tsarx 3 regimenes 
  ## tsar3.simux=function (nob, p1, p2, p3, P1, P2, P3, q1, q2, q3, ph.1, ph.2, ph.3, PH.1, PH.2, PH.3, qh.1, qh.2, qh.3, sig.1, sig.2, sig.3, lagd, thres.1=thres.1, thres.2=thres.2, lagp1, lagp2, lagp3, lagP1, lagP2, lagP3, lagq1, lagq2, lagq3, thresVar, s) 
  
  #xx=xx$yt   ### si hay una lista en el function del tsarx.
  #thresVar<-z[5001:nmax]
  #x<-xx[5001:nmax]
  
  #### para datos reales  x, thresVar
  
  x=Xt
  thresVar=Zt
  
  out1<-BAYESE.ARX(x, lagp1.1, lagP1.1, lagq1.1, Iteration, Burnin, constant, thresVar, s)
  out2<-BAYES2E.TARX(x, lagp1.2, lagp2.2, lagP1.2, lagP2.2,  lagq1.2, lagq2.2, Iteration, Burnin, step.thv, h, constant, thresVar, s, d0)
  out3<-BAYES3E.TARX(x, lagp1.3, lagp2.3, lagp3.3, lagP1.3, lagP2.3, lagP3.3,  lagq1.3, lagq2.3, lagq3.3, Iteration, Burnin, constant, step.thv, h, thresVar, s, d0)
  
  par.setlog <- matrix(NA, nrow =(Iteration-Burnin), ncol =regimenes)
  
  par.setlog[,1]<-out1$log.ver
  par.setlog[,2]<-out2$log.ver
  par.setlog[,3]<-out3$log.ver
  
  par.setlog2 <- matrix(NA, nrow =(Iteration-Burnin), ncol =regimenes)
  par.setlog3 <- matrix(NA, nrow =(Iteration-Burnin), ncol =regimenes)
  
  for (i in 1:(Iteration-Burnin))
  {
    for (j in 1:regimenes)
    {
      par.setlog2[i,j]<-exp(par.setlog[i,j]-max(par.setlog[i,]))
    }
  }
  
  
  for (i in 1:(Iteration-Burnin))
  {
    for (j in 1:regimenes)
    {
      par.setlog3[i,j]<-(par.setlog2[i,j]/sum(par.setlog2[i,]) )
    }
  }
  
  
  for (j in 1:regimenes)
  {
    probapost[k,j]<-(sum(par.setlog3[,j])/(Iteration-Burnin))
  }
  
  
  
  criterioCONGDON[k]<-which.max(probapost[k,])
  metodoCong[k]<-probapost[k,criterioCONGDON[k]]
  
  A[k,]<-cbind(out1$DIC,out2$DIC, out3$DIC)
  criterioDIC[k]<-which.min(A[k,])
  metodoDIC[k]<-A[k,criterioDIC[k]]
  
  B[k,]<-cbind(out1$NAIC,out2$NAIC,out3$NAIC)
  criterioNAIC[k]<-which.min(B[k,])
  metodoNAIC[k]<-B[k,criterioNAIC[k]]
  
}     ###  fin del repe





###############   SALIDAS CONGDON


(probapost)
(A)
(B)


#Con d=6, se obtiene que el mejor modelo es el de 2 regímenes

#Estimación final
set.seed(625)
replicas=1

Iteration<-12000
Burnin<-4000

x<-Xt
thresVar<-Zt

lagp1.3<-1
lagP1.3<-1
lagq1.3<-1
lagp2.3<-1
lagP2.3<-1:2
lagq2.3<-1
lagp3.3<-1
lagP3.3<-1
lagq3.3<-1
constant=1
h=25
s=4
d0=3
step.thv=0.04

out3<-BAYES3E.TARX(x, lagp1.3, lagp2.3, lagp3.3, lagP1.3, lagP2.3, lagP3.3,  lagq1.3, lagq2.3, lagq3.3, Iteration, Burnin, constant, step.thv, h, thresVar, s, d0)
################### diagnósticos con los residuales 


#####   res es donde se guardan los residuales, tener cuidado que la serie residual no posea NAs.
res=out3$residual.est
par(mfrow=c(2,1))
ts.plot(res,ylab="Resiudales estandarizados", xlab="Tiempo")   # VALIDAR SUPUESTOS CON RESIDUALES, de aquí en adelante...
hist(res,main="Histograma de residuales estandarizados")
par(mfrow=c(2,2))
acf(res, main="I",xlab="Tiempo",lag.max=50)        # función de autocorrelación muestral
pacf(res, main="II",xlab="Tiempo",ylab="PACF",lag.max=50)       # función de autocorrelación parcial muestral

jarque.bera.test(res) # prueba de normalidad

B=matrix(NA,nrow=36,ncol=1)
for (i in 1:36) {
  A=Box.test(res, lag = i, type = "Ljung-Box")
  B[i,1]=A$p.value
}
B

##########################



# Prueba CUSUM y CUSUM-SQ para los residuales del modelo (evidencia de una especifi
#cación correcta o no del modelo y heterocedasticidad, resp.)


# Prueba CUSUM y CUSUM-SQ para los residuales del modelo (evidencia de una especifi
#cación correcta o no del modelo y heterocedasticidad, resp.)
par(mfrow=c(2,1))
cum=cumsum(res)/sd(res)
N=length(res)
cumq=cumsum(res^2)/sum(res^2)
Af=0.948 ###Cuantil del 95% para la estad?stica cusum
co=0.13821####Valor del cuantil aproximado para cusumsq para n/2
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

##########################################################################
#Estimación modelo AR variable de umbral
par(mfrow=c(2,1))
forecast::Acf(Zt, main="",xlab="Tiempo",lag.max=50)        # función de autocorrelación muestral
forecast::Pacf(Zt, main="",xlab="Tiempo",lag.max=50)       # función de autocorrelación parcial muestral
par(mfrow=c(1,1))
plot(armasubsets(Zt,nar=30,nma=0))
plot(Zt)
Modelo.zt=forecast::Arima(Zt,order=c(1,0,0),include.constant = T,fixed=c(NA,NA))
lmtest::coeftest(Modelo.zt)
summary(Modelo.zt)

##################################################### PRON?STICOS PARA MODELOS ESTACIONAL MULTIPLICATIVOS 


##################################################### PRON?STICOS PARA MODELOS ESTACIONAL MULTIPLICATIVOS 


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



#################################################


######################################       PARA DATOS REALES



pronosticos<-function(LH, x, thresVar, Iteration, Burnin, step.thv, d0)
{
  
  
  L=3           # n?mero de reg?menes
  nx=length(x)
  
  lagp1=1
  lagp2=1
  lagp3=1
  lagP1=1
  lagP2=1:2
  lagP3=1
  lagq1=1
  lagq2=1
  lagq3=1
  
  
  lagpr<-vector("list",L)
  lagPr<-vector("list",L)
  lagqr<-vector("list",L)
  
  lagpr[[1]]<-lagp1
  lagpr[[2]]<-lagp2
  lagpr[[3]]<-lagp3
  lagPr[[1]]<-lagP1
  lagPr[[2]]<-lagP2
  lagPr[[3]]<-lagP3
  lagqr[[1]]<-lagq1
  lagqr[[2]]<-lagq2
  lagqr[[3]]<-lagq3
  
  p1 <- length(lagp1)
  p2 <- length(lagp2)
  p3 <- length(lagp3)
  P1 <- length(lagP1)
  P2 <- length(lagP2)
  P3 <- length(lagP3)
  q1 <- length(lagq1)
  q2 <- length(lagq2)
  q3 <- length(lagq3)
  
  
  NN<-Iteration-Burnin
  constant<-1
  h<-25
  s=4
  
  oarp=c(p1,p2,p3)       ## ordenes autorregresivos para los dos reg?menes
  oarP=c(P1,P2,P3) 
  oarq=c(q1,q2,q3)       ## ordenes autorregresivos exogenos para los dos reg?menes
  
  
  
  
  out3<-BAYES3E.TARX(x, lagp1, lagp2, lagp3, lagP1, lagP2, lagP3,  lagq1, lagq2, lagq3, Iteration, Burnin, constant, step.thv, h, thresVar, s, d0)
  salida3=out3$posterior
  
  
  conppron=vector("list",L)
  parppron=vector("list",L)
  parPpron=vector("list",L)
  parqpron=vector("list",L)
  sigpron=vector("list",L)
  
  if (constant==1)
  {
    conppron[[1]]=salida3[,1]
    parppron[[1]]=salida3[,2:(p1+constant)]
    parPpron[[1]]=salida3[,(p1+constant+1):(p1+constant+P1)]
    parqpron[[1]]=salida3[,(p1+constant+P1+1):(p1+constant+P1+q1)]
    conppron[[2]]=salida3[,p1+constant+P1+q1+1]
    parppron[[2]]=salida3[,(p1+constant+P1+q1+1+1):(p1+constant+P1+q1+p2+constant)]
    parPpron[[2]]=salida3[,(p1+constant+P1+q1+p2+constant+1):(p1+constant+P1+q1+p2+constant+P2)]
    parqpron[[2]]=salida3[,(p1+constant+P1+q1+p2+constant+P2+1):(p1+constant+P1+q1+p2+constant+P2+q2)]
    conppron[[3]]=salida3[,p1+constant+P1+q1+p2+constant+P2+q2+1]
    parppron[[3]]=salida3[,(p1+constant+P1+q1+p2+constant+P2+q2+1+1):(p1+constant+P1+q1+p2+constant+P2+q2+p3+constant)]
    parPpron[[3]]=salida3[,(p1+constant+P1+q1+p2+constant+P2+q2+p3+constant+1):(p1+constant+P1+q1+p2+constant+P2+q2+p3+constant+P3)]
    parqpron[[3]]=salida3[,(p1+constant+P1+q1+p2+constant+P2+q2+p3+constant+P3+1):(p1+constant+P1+q1+p2+constant+P2+q2+p3+constant+P3+q3)]
    
    sigpron[[1]]=salida3[,p1+constant+P1+q1+p2+constant+P2+q2+p3+constant+P3+q3+1]
    sigpron[[2]]=salida3[,p1+constant+P1+q1+p2+constant+P2+q2+p3+constant+P3+q3+2]
    sigpron[[3]]=salida3[,p1+constant+P1+q1+p2+constant+P2+q2+p3+constant+P3+q3+3]
    
    thres.1=salida3[,p1+constant+P1+q1+p2+constant+P2+q2+p3+constant+P3+q3+4]
    thres.2=salida3[,p1+constant+P1+q1+p2+constant+P2+q2+p3+constant+P3+q3+5]
    
    lagd=salida3[,p1+constant+P1+q1+p2+constant+P2+q2+p3+constant+P3+q3+6]
    
  }
  
  if (constant==0)
  {
    conppron[[1]]=matrix(0,nrow=(Iteration-Burnin),ncol=1)
    parppron[[1]]=salida3[,1:p1]
    parPpron[[1]]=salida3[,(p1+1):(p1+P1)]
    parqpron[[1]]=salida3[,(p1+P1+1):(p1+P1+q1)]
    conppron[[2]]=matrix(0,nrow=(Iteration-Burnin),ncol=1)
    parppron[[2]]=salida3[,(p1+P1+q1+1):(p1+P1+q1+p2)]
    parPpron[[2]]=salida3[,(p1+P1+q1+p2+1):(p1+P1+q1+p2+P2)]
    parqpron[[2]]=salida3[,(p1+P1+q1+p2+P2+1):(p1+P1+q1+p2+P2+q2)]
    conppron[[3]]=matrix(0,nrow=(Iteration-Burnin),ncol=1)
    parppron[[3]]=salida3[,(p1+P1+q1+p2+P2+q2+1):(p1+P1+q1+p2+P2+q2+p3)]
    parPpron[[3]]=salida3[,(p1+P1+q1+p2+P2+q2+p3+1):(p1+P1+q1+p2+P2+q2+p3+P3)]
    parqpron[[3]]=salida3[,(p1+P1+q1+p2+P2+q2+p3+P3+1):(p1+P1+q1+p2+P2+q2+p3+P3+q3)]
    
    sigpron[[1]]=salida3[,p1+P1+q1+p2+P2+q2+p3+P3+q3+1]
    sigpron[[2]]=salida3[,p1+P1+q1+p2+P2+q2+p3+P3+q3+2]
    sigpron[[3]]=salida3[,p1+P1+q1+p2+P2+q2+p3+P3+q3+3]
    
    thres.1=salida3[,p1+P1+q1+p2+P2+q2+p3+P3+q3+4]
    thres.2=salida3[,p1+P1+q1+p2+P2+q2+p3+P3+q3+5]
    
    lagd=salida3[,p1+P1+q1+p2+P2+q2+p3+P3+q3+6]
    
  }
  
  seriex=matrix(NA,nrow=NN, ncol=LH)
  seriez=matrix(NA,nrow=NN, ncol=LH)
  
  for (i in 1:NN)
  {
    
    xv=ts(rep(NA,nx+LH))
    xv[1:nx]=x
    zv=ts(rep(NA,nx+LH))
    zv[1:nx]=thresVar
    
    for (hh in 1:LH)
    {
      zv[nx+hh]=0.5853+0.5335*zv[nx+hh-1]+rnorm(1, mean=0, sd=sqrt(0.3048))   ## SE CAMBIA LA FORMULA, el kernel de transici?n, variable umbral
    }
    
    
    
    for (h in 1:LH)
    {
      
      if (zv[nx-lagd[i]+h]<=thres.1[i]){
        
        SJ<-1
      }
      if (zv[nx-lagd[i]+h]>thres.1[i]  &  zv[nx-lagd[i]+h]<=thres.2[i] ){
        
        SJ<-2
      }
      if (zv[nx-lagd[i]+h]>thres.2[i]){
        
        SJ<-3
      }
      
      if (ncol(t(t(parppron[[SJ]])))!=1)                          
      {
        X1=0
        for (k in 1:oarp[SJ])
        {
          X1=X1+parppron[[SJ]][i,k]*xv[nx+h-lagpr[[SJ]][k]]
        }
      }
      if (ncol(t(t(parppron[[SJ]])))==1) 
      {
        X1=0
        for (k in 1:oarp[SJ])
        {
          X1=X1+parppron[[SJ]][i]*xv[nx+h-lagpr[[SJ]][k]]
        }
      }
      if (ncol(t(t(parPpron[[SJ]])))!=1)                          
      {
        XX1=0
        for (K in 1:oarP[SJ])
        {
          XX1=XX1+parPpron[[SJ]][i,K]*xv[nx+h-s*lagPr[[SJ]][K]]
        }
      }
      
      if (ncol(t(t(parPpron[[SJ]])))==1) 
      {
        XX1=0
        for (K in 1:oarP[SJ])
        {
          XX1=XX1+parPpron[[SJ]][i]*xv[nx+h-s*lagPr[[SJ]][K]]
        }
      }
      if (ncol(t(t(parppron[[SJ]])))!=1 & ncol(t(t(parPpron[[SJ]])))!=1)                          
      {
        YY1=0
        for (K in 1:oarP[SJ]){
          for (k  in 1:oarp[SJ]){
            YY1=YY1 + parPpron[[SJ]][i,K]*parppron[[SJ]][i,k]*xv[nx+h-(lagpr[[SJ]][k]+s*lagPr[[SJ]][K])]
          }
        }
      }
      if (ncol(t(t(parppron[[SJ]])))!=1 & ncol(t(t(parPpron[[SJ]])))==1)                          
      {
        YY1=0
        for (K in 1:oarP[SJ]){
          for (k  in 1:oarp[SJ]){
            YY1=YY1 + parPpron[[SJ]][i]*parppron[[SJ]][i,k]*xv[nx+h-(lagpr[[SJ]][k]+s*lagPr[[SJ]][K])]
          }
        }
      }
      if (ncol(t(t(parppron[[SJ]])))==1 & ncol(t(t(parPpron[[SJ]])))!=1)                          
      {
        YY1=0
        for (K in 1:oarP[SJ]){
          for (k  in 1:oarp[SJ]){
            YY1=YY1 + parPpron[[SJ]][i,K]*parppron[[SJ]][i]*xv[nx+h-(lagpr[[SJ]][k]+s*lagPr[[SJ]][K])]
          }
        }
      }
      if (ncol(t(t(parppron[[SJ]])))==1 & ncol(t(t(parPpron[[SJ]])))==1)   
      {
        YY1=0
        for (K in 1:oarP[SJ]){
          for (k  in 1:oarp[SJ]){
            YY1=YY1 + parPpron[[SJ]][i]*parppron[[SJ]][i]*xv[nx+h-(lagpr[[SJ]][k]+s*lagPr[[SJ]][K])]
          }
        }
      }
      if (ncol(t(t(parqpron[[SJ]])))!=1)                          
      {
        XXX1=0
        for (kk in 1:oarq[SJ])
        {
          XXX1=XXX1+parqpron[[SJ]][i,kk]*zv[nx+h-lagqr[[SJ]][kk]]
        }
      }
      if (ncol(t(t(parqpron[[SJ]])))==1) 
      {
        XXX1=0
        for (kk in 1:oarq[SJ])
        {
          XXX1=XXX1+parqpron[[SJ]][i]*zv[nx+h-lagqr[[SJ]][kk]]
        }
      }
      
      
      xv[nx+h]=sum(conppron[[SJ]][i], X1, XX1, -YY1, XXX1, rnorm(1, mean=0,sd=sqrt(sigpron[[SJ]][i])))
      
      seriex[i,h]=xv[nx+h]
      seriez[i,h]=zv[nx+h]
      
    }
  }
  pron<-list(seriex=seriex, seriez=seriez)
  return(pron)
  
}





###########Pronósticos un paso adelante

### CORRIDA PARA OBTENER PRON?STICOS
LH=1
Iteration=20000
Burnin=8000
d0=3
step.thv=0.04
AA<-matrix(NA,nrow=15, ncol=LH)


for (i in 0:14) {
  set.seed(625)
  Base=fread("Desempleo_uk.csv",sep=",")
  Datos=ts(Base[1:(132+(i)),2],start=c(1983,2),freq=4)
  Xt=diff((Datos))
  pib=fread("PIB_uk.csv",sep=",")
  Zt=ts(pib[34:(166+(i)),2],start = c(1983,2),freq=4)
  Zt=diff(log(Zt))*100
  x2=Xt
  thresVar2=Zt
  
  p=pronosticos(LH, x2, thresVar2, Iteration, Burnin, step.thv, d0)
  px=p$seriex
  pz=p$seriez
  AA[i+1,]= (tar.summarymedia(px)[1])
  
}


Pronostico=ts(AA[,1],start=c(2016,3),freq=4)
Comparacion=fread("Desempleo_uk.csv",sep=",")
Comparacion=Comparacion[132:147,2,]
Comp_des=ts(Comparacion,start=c(2016,2),freq=4)
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
write.xlsx(data,"D:/sarbelaez/Documents/Maestría/Tesis/Datos finales/Resultados/Pronosticos_1_desempleo_pib_uk.xlsx",overwrite = T)


###########Pronósticos dos pasos adelante

### CORRIDA PARA OBTENER PRON?STICOS

LH=2
Iteration=20000
Burnin=8000
d0=3
step.thv=0.04
AA<-matrix(NA,nrow=8, ncol=LH)

for (i in 0:7) {
  set.seed(625)
  Base=fread("Desempleo_uk.csv",sep=",")
  Datos=ts(Base[1:(132+(2*i)),2],start=c(1983,2),freq=4)
  Xt=diff((Datos))
  pib=fread("PIB_uk.csv",sep=",")
  Zt=ts(pib[34:(166+(2*i)),2],start = c(1983,2),freq=4)
  Zt=diff(log(Zt))*100
  x2=Xt
  thresVar2=Zt
  p=pronosticos(LH, x2, thresVar2, Iteration, Burnin, step.thv, d0)
  px=p$seriex
  pz=p$seriez
  AA[i+1,]= t(tar.summarymedia(px)[,1])
  
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

Pronostico=ts(CC[,1],start=c(2016,3),freq=4)
Comparacion=fread("Desempleo_uk.csv",sep=",")
Comparacion=Comparacion[132:147,2,]
Comp_des=ts(Comparacion,start=c(2016,2),freq=4)
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
write.xlsx(data,"D:/sarbelaez/Documents/Maestría/Tesis/Datos finales/Resultados/Pronosticos_2_desempleo_pib_uk.xlsx",overwrite = T)



###########Pronósticos tres pasos adelante

### CORRIDA PARA OBTENER PRON?STICOS
LH=3
Iteration=20000
Burnin=8000
d0=3
step.thv=0.04
AA<-matrix(NA,nrow=5, ncol=LH)

for (i in 0:4) {
  set.seed(625)
  Base=fread("Desempleo_uk.csv",sep=",")
  Datos=ts(Base[1:(132+(3*i)),2],start=c(1983,2),freq=4)
  Xt=diff((Datos))
  pib=fread("PIB_uk.csv",sep=",")
  Zt=ts(pib[34:(166+(3*i)),2],start = c(1983,2),freq=4)
  Zt=diff(log(Zt))*100
  x2=Xt
  thresVar2=Zt
  p=pronosticos(LH, x2, thresVar2, Iteration, Burnin, step.thv, d0)
  px=p$seriex
  pz=p$seriez
  AA[i+1,]= t(tar.summarymedia(px)[,1])
  
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


Pronostico=ts(CC[,1],start=c(2016,3),freq=4)
Comparacion=fread("Desempleo_uk.csv",sep=",")
Comparacion=Comparacion[132:147,2,]
Comp_des=ts(Comparacion,start=c(2016,2),freq=4)
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
write.xlsx(data,"D:/sarbelaez/Documents/Maestría/Tesis/Datos finales/Resultados/Pronosticos_3_desempleo_pib_uk.xlsx",overwrite = T)

###########Pronósticos cuatro pasos adelante

### CORRIDA PARA OBTENER PRON?STICOS
LH=4
Iteration=20000
Burnin=8000
d0=3
step.thv=0.04
AA<-matrix(NA,nrow=4, ncol=LH)

for (i in 0:3) {
  set.seed(625)
  Base=fread("Desempleo_uk.csv",sep=",")
  Datos=ts(Base[1:(132+(4*i)),2],start=c(1983,2),freq=4)
  Xt=diff((Datos))
  pib=fread("PIB_uk.csv",sep=",")
  Zt=ts(pib[34:(166+(4*i)),2],start = c(1983,2),freq=4)
  Zt=diff(log(Zt))*100
  x2=Xt
  thresVar2=Zt
  p=pronosticos(LH, x2, thresVar2, Iteration, Burnin, step.thv, d0)
  px=p$seriex
  pz=p$seriez
  AA[i+1,]= t(tar.summarymedia(px)[,1])
  
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

Pronostico=ts(CC[,1],start(2016,3),freq=4)
Comparacion=fread("Desempleo_uk.csv",sep=",")
Comparacion=Comparacion[132:147,2,]
Comp_des=ts(Comparacion,start=c(2016,2),freq=4)
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
write.xlsx(data,"D:/sarbelaez/Documents/Maestría/Tesis/Datos finales/Resultados/Pronosticos_4_desempleo_pib_uk.xlsx",overwrite = T)

