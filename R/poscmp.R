poscmp<-function(s,s2=NULL,rc=rep(FALSE,length=length(s2)),maxN=NULL,
                  K=2*max(c(s,s2)), nk=NULL, n=length(s), n2=length(s2),
                  mean.prior.degree=7, sd.prior.degree=3,
                  df.mean.prior=1, df.sd.prior=5,
                  beta0.mean.prior=-3, beta1.mean.prior=0,
                  beta0.sd.prior=10, beta1.sd.prior=10,
                  mem.optimism.prior=1, df.mem.optimism.prior=5, 
                  mem.sd.prior=5, df.mem.sd.prior=3, 
                  muproposal=0.1, 
                  sigmaproposal=0.15, 
                  beta0proposal=0.1, beta1proposal=0.001,
                  memmuproposal=0.1, memsdproposal=0.15,
                  visibility=TRUE,
                  Np=0,
                  samplesize=10,burnin=0,interval=1,burnintheta=500,burninbeta=20,
                  priorsizedistribution=c("beta","nbinom","pln","flat","supplied"),
                  mean.prior.size=NULL, sd.prior.size=NULL,
                  mode.prior.sample.proportion=NULL,
                  median.prior.sample.proportion=NULL,
                  median.prior.size=NULL,
                  mode.prior.size=NULL,
                  quartiles.prior.size=NULL,
                  effective.prior.df=1,
                  alpha=NULL,
                  seed=NULL,
                  maxbeta=120,
                  supplied=list(maxN=maxN),
              num.recruits=NULL,
              recruit.times=NULL,
              max.coupons=NULL,
                  verbose=TRUE){
    #this function takes a vector of population sizes and a vector s of 
    #sequential sizes of sampled units and returns a log likelihood value
    #s values must all be positive integers
    if(!is.null(seed))  set.seed(as.integer(seed))
    #
    # Cap the maximum degree to K
    #
    s[s>K] <- K
    if(is.null(nk)){nk=tabulate(s,nbins=K)}
    if(!is.null(s2)) s2[s2>K] <- K
    #
    # Transform observed mean parametrization to log-normal
    # parametrization
    #
    out <- cmp.natural(mu=mean.prior.degree, sigma=sd.prior.degree)
    mu <- log(out$lambda)
    sigma <- out$nu
#   sigma <- max(0.00001, sigma)
    #
    if(visibility){
      dimsample <- 5+Np+4
    }else{
      dimsample <- 5+Np
    }
    #
    # Determine if we are in the two-sample case or the one-sample
    if(!is.null(s2)){
     n1 = n
     n0 = sum(rc)
     n = n1 + n2 - n0 # The number of unique people seen
    }
    #
    priorsizedistribution=match.arg(priorsizedistribution)
    prior <- dsizeprior(n=n,
                  type=priorsizedistribution,
                  sd.prior.size=sd.prior.size,
                  mode.prior.sample.proportion=mode.prior.sample.proportion,
                  median.prior.sample.proportion=median.prior.sample.proportion,
                  median.prior.size=median.prior.size,
                  mode.prior.size=mode.prior.size,
                  mean.prior.size=mean.prior.size,
                  quartiles.prior.size=quartiles.prior.size,
                  effective.prior.df=effective.prior.df,
                  alpha=alpha,
                  maxN=maxN,
                  maxbeta=maxbeta,
                  log=TRUE,
                  supplied=supplied,
                  verbose=verbose)
    if(!is.null(s2)){
      Cret <- .C("gcmp2",
              pop12=as.integer(c(s, s2[!rc], rep(0,prior$maxN-length(s)-length(s2[!rc])))),
              pop21=as.integer(c(s2,sum(s)-sum(s2[rc]), rep(0,prior$maxN-length(s2)-1))),
              nk=as.integer(nk),
              K=as.integer(K),
              n1=as.integer(n1),
              n2=as.integer(n2),
              n0=as.integer(n0),
              samplesize=as.integer(samplesize),
              burnin=as.integer(burnin),
              interval=as.integer(interval),
              mu=as.double(mu), df.mean.prior=as.double(df.mean.prior),
              sigma=as.double(sigma), df.sd.prior=as.double(df.sd.prior),
              Np=as.integer(Np),
              muproposal=as.double(muproposal),
              sigmaproposal=as.double(sigmaproposal),
              N=as.integer(prior$N),
              maxN=as.integer(prior$maxN),
              sample=double(samplesize*dimsample),
              ppos=double(K),
              lpriorm=as.double(prior$lprior),
              burnintheta=as.integer(burnintheta),
              burninbeta=as.integer(burninbeta),
              verbose=as.integer(verbose), PACKAGE="sspse")
    }else{
     if(visibility){
      Cret <- .C("gcmpvis",
              pop=as.integer(c(s,rep(0,prior$maxN-n))),
              nk=as.integer(nk),
              K=as.integer(K),
              n=as.integer(n),
              samplesize=as.integer(samplesize),
              burnin=as.integer(burnin),
              interval=as.integer(interval),
              mu=as.double(mean.prior.degree), df.mean.prior=as.double(df.mean.prior),
              sigma=as.double(sd.prior.degree), df.sd.prior=as.double(df.sd.prior),
              beta0.mean.prior=as.double(beta0.mean.prior), beta0.sd.prior=as.double(beta0.sd.prior),
              beta1.mean.prior=as.double(beta1.mean.prior), beta1.sd.prior=as.double(beta1.sd.prior),
              mem.optimism.prior=as.double(log(mem.optimism.prior)), df.mem.optimism.prior=as.double(df.mem.optimism.prior),
              mem.sd.prior=as.double(mem.sd.prior), df.mem.sd.prior=as.double(df.mem.sd.prior),
              Np=as.integer(Np),
              srd=as.integer(s),
              numrec=as.double(num.recruits),
              rectime=as.double(recruit.times),
              maxcoupons=as.integer(max.coupons),
              muproposal=as.double(muproposal),
              sigmaproposal=as.double(sigmaproposal),
              beta0proposal=as.double(beta0proposal), beta1proposal=as.double(beta1proposal),
              memmuproposal=as.double(memmuproposal), memsdproposal=as.double(memsdproposal),
              N=as.integer(prior$N),
              maxN=as.integer(prior$maxN),
              sample=double(samplesize*dimsample),
              vsample=integer(samplesize*n),
              ppos=double(K),
              lpriorm=as.double(prior$lprior),
              burnintheta=as.integer(burnintheta),
              burninbeta=as.integer(burninbeta),
              verbose=as.integer(verbose), PACKAGE="sspse")
     }else{
      Cret <- .C("gcmp",
              pop=as.integer(c(s,rep(0,prior$maxN-n))),
              nk=as.integer(nk),
              K=as.integer(K),
              n=as.integer(n),
              samplesize=as.integer(samplesize),
              burnin=as.integer(burnin),
              interval=as.integer(interval),
              mu=as.double(mean.prior.degree), df.mean.prior=as.double(df.mean.prior),
              sigma=as.double(sd.prior.degree), df.sd.prior=as.double(df.sd.prior),
              Np=as.integer(Np),
              muproposal=as.double(muproposal),
              sigmaproposal=as.double(sigmaproposal),
              N=as.integer(prior$N),
              maxN=as.integer(prior$maxN),
              sample=double(samplesize*dimsample),
              ppos=double(K),
              lpriorm=as.double(prior$lprior),
              burnintheta=as.integer(burnintheta),
              verbose=as.integer(verbose), PACKAGE="sspse")
     }
    }
    Cret$sample<-matrix(Cret$sample,nrow=samplesize,ncol=dimsample,byrow=TRUE)
    degnames <- NULL
    if(Np>0){degnames <- c(degnames,paste("pdeg",1:Np,sep=""))}
    if(visibility){
     colnamessample <- c("N","mu","sigma","degree1","totalsize","beta0","beta1","mem.optimism","mem.sd")
     Cret$vsample<-matrix(Cret$vsample,nrow=samplesize,ncol=n,byrow=TRUE)
     colnames(Cret$vsample) <- 1:n
     max.mu <- 3*median(Cret$vsample)
     if(length(degnames)>0){
      colnames(Cret$sample) <- c(colnamessample, degnames)
     }else{
      colnames(Cret$sample) <- colnamessample
     }
     Cret$sample[,"mem.optimism"] <- exp(Cret$sample[,"mem.optimism"])
    }else{
     colnamessample <- c("N","mu","sigma","degree1","totalsize")
     max.mu <- 2*mean.prior.degree
     if(length(degnames)>0){
      colnames(Cret$sample) <- c(colnamessample, degnames)
     }else{
      colnames(Cret$sample) <- colnamessample
     }
    }
    #
    # Transform observed mean parametrization to log-normal
    # parametrization
    #
    # Expectation and s.d. of normal from log-normal
    #
    Cret$sample[,"mu"] <- exp(Cret$sample[,"mu"])
    Cret$sample <- cbind(Cret$sample,Cret$sample[,c("mu","sigma")])
    colnames(Cret$sample)[ncol(Cret$sample)-(1:0)] <- c("lambda","nu")
    # Transform to mean value parametrization 
    a <- t(apply(Cret$sample[,c("mu","sigma")],1,cmp.mu, max.mu=max.mu))
    nas <- apply(a,1,function(x){any(is.na(x))})
    if(!all(nas)){
     inas <- sample(seq_along(nas)[!nas],size=sum(nas),replace=TRUE)
     a[nas,] <- a[inas,]
#    Cret$sample[,c("mu","sigma")] <- t(apply(Cret$sample[,c("mu","sigma")],1,cmp.mu,max.mu=5*mean.prior.degree)))
     Cret$sample[,c("mu","sigma")] <- a
    }else{
      warning(paste("All the lambda and nu parameters are extreme. mean and sigma are on the natural scale."), call. = FALSE)
    }
#   # PLN mean
#   Cret$sample <- cbind(Cret$sample,Cret$sample[,c("mem.optimism")])
#   colnames(Cret$sample)[ncol(Cret$sample)] <- c("mem.degree.mean")
#   mean.degree <- sum(seq(along=Cret$nk)*Cret$ppos)
#   print(mean.degree)
#   Cret$sample[,"mem.degree.mean"] <- exp(log(mean.degree)+Cret$sample[,"mem.optimism"]+0.5*Cret$sample[,"mem.sd"])
    #
#   Cret$Nk<-Cret$nk/sum(Cret$nk)
    Cret$predictive.degree.count<-Cret$nk / samplesize
    Cret$nk<-NULL
    Cret$predictive.degree<-Cret$ppos
    Cret$ppos<-NULL
    endrun <- burnin+interval*(samplesize-1)
    attr(Cret$sample, "mcpar") <- c(burnin+1, endrun, interval)
    attr(Cret$sample, "class") <- "mcmc"
    ### compute modes of posterior samples,Maximum A Posterior (MAP) values N, mu, sigma, degree1
    Cret$MAP <- apply(Cret$sample,2,mode.density)
    Cret$MAP["N"] <- mode.density(Cret$sample[,"N"],lbound=n,ubound=prior$maxN)
    if(!is.null(s2)){Cret$n <- Cret$n1 +  Cret$n2 - Cret$n0}
#
#   Cret$MSE <- c(((prior$x-mean.prior.degree)^2)*prior$lprior/sum(prior$lprior),mean((Cret$sample[,"N"]-mean.prior.degree)^2))
    Cret$maxN <- prior$maxN
    Cret$quartiles.prior.size <- prior$quartiles.prior.size
    Cret$mode.prior.size <- prior$mode.prior.size
    Cret$mean.prior.size <- prior$mean.prior.size
    Cret$effective.prior.df <- prior$effective.prior.df
    Cret$median.prior.size <- prior$median.prior.size
    Cret$mode.prior.sample.proportion <- prior$mode.prior.sample.proportion
    Cret$N <- prior$N
    Cret
}
