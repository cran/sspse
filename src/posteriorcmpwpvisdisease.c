/*******************************************************************/
/* Computation of the log-likelihood and marginal posterior of size*/
/*******************************************************************/

#include "posteriorcmpwpvisdisease.h"
#include "cmp.h"
#include <R.h>
#include <Rmath.h>
#include <math.h>

void gcmpwpvisdisease (int *pop, int *dis,
            int *K,
            int *n,
            int *samplesize, int *warmup, int *interval,
            double *mu0, double *mu1, double *dfmu,
            double *sigma0, double *sigma1,
	    double *dfsigma,
            double *lnlam0, double *lnlam1,
            double *nu0, double *nu1,
            double *beta0muprior, double *beta0sigmaprior,
            double *betatmuprior, double *betatsigmaprior,
            double *betaumuprior, double *betausigmaprior,
            double *lmemmu,
            double *memnu,
            double *memdfmu, double *memdfnu,
            double *memod,
            int *Np0i, int *Np1i,
            int *srd,
            int *numrec,
            double *rectime,
            int *maxcoupons,
            double *lnlamproposal,
            double *nuproposal,
            double *beta0proposal, double *betatproposal, double *betauproposal,
            double *tauproposal,
            double *lmemmuproposal, double *memnuproposal,
            int *N, int *maxN,
            double *sample,
            int *vsample,
            double *pos0u, double *pos1u,
            double *pos0d, double *pos1d,
            double *lpriorm,
            int *warmuptheta,
            int *warmupbeta,
            int *verbose
                         ) {
  int dimsample, Np0, Np1;
  int step, staken, getone=1, intervalone=1, verboseMHcmp = 0;
  int i, ni, Ni, Ki, isamp, iinterval, isamplesize, iwarmup;
  int j, k;
  int umax;
  double alpha, pnb, rnb;
  double dsamp;
  double mu0i, sigma0i, lnlam0i, nu0i;
  double mu1i, sigma1i, lnlam1i, nu1i;
  double tau, tau0, tau1, ptau;
  double sigma2i;
  double dlmemmu, dmemnu;
  double dbeta0, dbetat, dbetau;
  double beta0i, betati, betaui;
  double lmemmui;
  double memmui, memnui;
  int tU, sizei, imaxN, imaxm, give_log0=0, give_log1=1;
  int discountn, discount;
  double r, pis, pis2, Nd;
  double gammart, gamma0rt, gamma1rt;
  double p0is, p1is;
  double temp, uprob;
  double lliki;
  int maxc;
  double errval=0.0000000001, lzcmp;

  GetRNGstate();  /* R function enabling uniform RNG */

  ni=(*n);
  Ni=(*N);
  Ki=(*K);
  imaxN=(*maxN);
  imaxm=imaxN-ni;
  isamplesize=(*samplesize);
  iinterval=(*interval);
  iwarmup=(*warmup);
  Np0=(*Np0i);
  Np1=(*Np1i);
  dbeta0=(*beta0muprior);
  dbetat=(*betatmuprior);
  dbetau=(*betaumuprior);
  dlmemmu=(*lmemmu);
  dmemnu=(*memnu);
  alpha=(*memod);
  maxc=(*maxcoupons);
  
  dimsample=18+Np0+Np1;
  pnb=(alpha-1.)/alpha;

  double *p0i = (double *) malloc(sizeof(double) * Ki);
  double *p1i = (double *) malloc(sizeof(double) * Ki);
  double *pd = (double *) malloc(sizeof(double) * Ki);
  double *pd2 = (double *) malloc(sizeof(double) * (10*Ki));
  int *u = (int *) malloc(sizeof(int) * imaxN);
  int *b = (int *) malloc(sizeof(int) * ni);
  int *Nk0 = (int *) malloc(sizeof(int) * Ki);
  int *Nk1 = (int *) malloc(sizeof(int) * Ki);
  int *nk0 = (int *) malloc(sizeof(int) * Ki);
  int *nk1 = (int *) malloc(sizeof(int) * Ki);
  int *Nk0pos = (int *) malloc(sizeof(int) * Ki);
  int *Nk1pos = (int *) malloc(sizeof(int) * Ki);
  double *lpm = (double *) malloc(sizeof(double) * imaxm);
  double *pdeg0i = (double *) malloc(sizeof(double) * (Np0+1));
  double *pdeg1i = (double *) malloc(sizeof(double) * (Np1+1));
  double *psample0 = (double *) malloc(sizeof(double) * (Np0+1));
  double *psample1 = (double *) malloc(sizeof(double) * (Np1+1));
  double *lnlamsample0 = (double *) malloc(sizeof(double) * isamplesize);
  double *lnlamsample1 = (double *) malloc(sizeof(double) * isamplesize);
  double *nusample0 = (double *) malloc(sizeof(double) * isamplesize);
  double *nusample1 = (double *) malloc(sizeof(double) * isamplesize);
  double *beta0sample = (double *) malloc(sizeof(double) * isamplesize);
  double *betatsample = (double *) malloc(sizeof(double) * isamplesize);
  double *betausample = (double *) malloc(sizeof(double) * isamplesize);
  double *lmemmusample = (double *) malloc(sizeof(double) * isamplesize);
  double *memnusample = (double *) malloc(sizeof(double) * isamplesize);
  double *tau0sample = (double *) malloc(sizeof(double) * isamplesize);
  double *tau1sample = (double *) malloc(sizeof(double) * isamplesize);

 //Rprintf("Started %d %d\n", dis[0], dis[1]);
  for (i=0; i<Ki; i++){
    nk0[i]=0;
    nk1[i]=0;
  }
  uprob=ni;
  for (i=0; i<ni; i++){
    if((pop[i]>0) && (pop[i] <= Ki)){ u[i]=pop[i];}
    if( pop[i]==0){ u[i]=1;}
    if( pop[i]>Ki){ u[i]=Ki; uprob--;}
    // Create sample counts from the data
    if( dis[i]==1 ){
      nk1[u[i]-1]=nk1[u[i]-1]+1;
    }else{
      nk0[u[i]-1]=nk0[u[i]-1]+1;
    }
  }
  uprob/=ni;
  uprob = 0.5 + uprob/2.0;
  b[ni-1]=u[ni-1];
  for (i=(ni-2); i>=0; i--){
    b[i]=b[i+1]+u[i];
  }
  for (i=0; i<Ki; i++){
     Nk0[i]=nk0[i];
     Nk0pos[i]=0;
     pos0u[i]=0.;
     pos0d[i]=0.;
     Nk1[i]=nk1[i];
     Nk1pos[i]=0;
     pos1u[i]=0.;
     pos1d[i]=0.;
  }
  for (i=ni; i<imaxN; i++){
    u[i]=u[(int)trunc(10*unif_rand()+ni-10)];
  }
  tU=0;
  for (i=ni; i<Ni; i++){
    tU+=u[i];
  }
  /* Draw initial phis */
  r=0.;
  discountn=0;
  for (i=0; i<ni; i++){
    r+=(exp_rand()/(tU+b[i]));
    discountn+=dis[i];
  }
  discount=discountn;
  for (i=ni; i<Ni; i++){
    discount+=dis[i];
  }

  tau0sample[0] = -1.386294;  // logit(0.2)
  tau0sample[0] = -6.57879;  // logit(0.082)
  tau1sample[0] =  0.62025;  // No impact of individual degree
  tau0sample[0] = -2.415478;  // logit(0.082)
  tau1sample[0] = 0.0;  // No impact of individual degree

  for (i=0; i<Np0; i++){
     psample0[i] = 0.01;
  }
  for (i=0; i<Np1; i++){
     psample1[i] = 0.01;
  }
  beta0sample[0] = dbeta0;
  betatsample[0] = dbetat;
  betausample[0] = dbetau;
  lmemmusample[0] = dlmemmu;
  memnusample[0] = dmemnu;
  lnlamsample0[0] = (*lnlam0);
  lnlamsample1[0] = (*lnlam1);
  nusample0[0] = (*nu0);
  nusample1[0] = (*nu1);

  isamp = 0;
  step = -iwarmup;
// Rprintf("Started %d %d\n", dis[0], dis[1]);
  while (isamp < isamplesize) {

    /* Draw new theta and tau */
    /* but less often than the other full conditionals */
    /*  */
    /* theta = (lnlam, nu))  while tau is the logit(prev) */
    /*  */
    if (step == -iwarmup || step % 10 == 0) { 
// Rprintf("Started %d %f\n", step, lnlamsample0[0]);
     MHcmpthetawpdisease(dis, u, Nk0,Nk1,K, &discount,
       mu0,mu1,dfmu,sigma0,sigma1,
       dfsigma,lnlamproposal,nuproposal,tauproposal,
       &Ni, &Np0, &Np1, psample0, psample1,
       lnlamsample0, nusample0,
       lnlamsample1, nusample1,
       tau0sample, tau1sample,
       &getone, &staken, warmuptheta, &intervalone, 
       &verboseMHcmp);
// Rprintf("Ended %d %d\n", step, discount);

 //  Sample 0 is taken as the sampler only draws one sample (as &getone =1)
     lnlam0i=lnlamsample0[0];
     lnlam1i=lnlamsample1[0];
     nu0i=nusample0[0];
     nu1i=nusample1[0];

     tau0=tau0sample[0];
     tau1=tau1sample[0];

     for (i=0; i<Np0; i++){
      pdeg0i[i] = psample0[i];
     }
     for (i=0; i<Np1; i++){
      pdeg1i[i] = psample1[i];
     }
    }

    /* Compute the unit distribution (given the new theta = (lnlam, nu)) */
    /* First for 0 */
    p0is=0.;
    lzcmp = zcmp(exp(lnlam0i), nu0i, errval, Ki, give_log1);
    if(lzcmp < -100000.0){continue;}
    p0i[Np0]=cmp(Np0+1,lnlam0i,nu0i,lzcmp,give_log0);
    p0is+=p0i[Np0];
    for (i=Np0+1; i<Ki; i++){
      p0i[i]=p0i[i-1]*exp(lnlam0i-nu0i*log((double)(i+1)));
      p0is+=p0i[i];
    }
    for (i=0; i<Ki; i++){
      p0i[i]/=p0is;
    }
    p0is=1.;
    for (i=0; i<Np0; i++){
      p0is-=pdeg0i[i];
    }
    for (i=0; i<Ki; i++){
      p0i[i]*=p0is;
    }
    // !!!!! Why this? For non-parametric piece
    for (i=0; i<Np0; i++){
      p0i[i]=pdeg0i[i];
    }
    /* Now for 1 */
    p1is=0.;
    lzcmp = zcmp(exp(lnlam1i), nu1i, errval, Ki, give_log1);
    if(lzcmp < -100000.0){continue;}
    p1i[Np1]=cmp(Np1+1,lnlam1i,nu1i,lzcmp,give_log0);
    p1is+=p1i[Np1];
    for (i=Np1+1; i<Ki; i++){
      p1i[i]=p1i[i-1]*exp(lnlam1i-nu1i*log((double)(i+1)));
      p1is+=p1i[i];
    }
    for (i=0; i<Ki; i++){
      p1i[i]/=p1is;
    }
    p1is=1.;
    for (i=0; i<Np1; i++){
      p1is-=pdeg1i[i];
    }
    for (i=0; i<Ki; i++){
      p1i[i]*=p1is;
    }
    // !!!!! Why this? For non-parametric piece
    for (i=0; i<Np1; i++){
      p1i[i]=pdeg1i[i];
    }

    // Now computes mean and s.d. from log-lambda and nu
    mu0i=0.0;
    sigma2i=0.0;
    for (i=0; i<Ki; i++){
      mu0i+=p0i[i]*(i+1);
      sigma2i+=p0i[i]*(i+1)*(i+1);
    }
    sigma2i=sigma2i-mu0i*mu0i;
    sigma0i = sqrt(sigma2i);

    mu1i=0.0;
    sigma2i=0.0;
    for (i=0; i<Ki; i++){
      mu1i+=p1i[i]*(i+1);
      sigma2i+=p1i[i]*(i+1)*(i+1);
    }
    sigma2i=sigma2i-mu1i*mu1i;
    sigma1i = sqrt(sigma2i);

// Rprintf("Started MHwpmemdisease %d %d %d\n", step, discount, *warmupbeta);
//
    /* Draw new beta using MCMC */
    /* This is the measurement error model component.  */
    /*                                                 */
    /* beta controls the measurement error model ("mem") */
    /* ("wp") weighted Poisson distribution */
    if (step == -iwarmup || step % 20 == 0) { 
     MHwpmemdisease(//dis,
       u, n, K, &Ni, &discount,
       beta0muprior,beta0sigmaprior,betatmuprior,betatsigmaprior, betaumuprior,betausigmaprior,
       lmemmu,memdfmu,
       memnu,memdfnu,
       srd,numrec,rectime,maxcoupons,
       beta0proposal,betatproposal,betauproposal,
       tauproposal, 
       lmemmuproposal,memnuproposal,
       beta0sample, betatsample, betausample, 
       lmemmusample,
       memnusample,
       tau0sample, tau1sample,
       &getone, &staken, warmupbeta, &intervalone, 
       &verboseMHcmp);
// Rprintf("Ended MHwpmemdisease %d %d\n", step, discount);
//  Sample 0 is taken as the sampler only draws one sample (as &getone = 1)
     beta0i=beta0sample[0];
     betati=betatsample[0];
     betaui=betausample[0];
     lmemmui=lmemmusample[0];
     memnui=memnusample[0];
// Rprintf("betaui %f betati %f beta0i %f\n", betaui, betati, beta0i);
     tau0=tau0sample[0];
     tau1=tau1sample[0];

    /* Draw true unit sizes based on the reported degrees*/
    // First reset counts
    for (i=0; i<Ki; i++){
     nk0[i]=0;
     nk1[i]=0;
    }
    umax = 0;
    for (j=0; j<ni; j++){
     if(srd[j] <= (10*Ki)){
//    Multiply by the Conway-Maxwell-Poisson PMF for observation
      for (i=0; i<Ki; i++){
       // Next to exclude unit sizes inconsistent with the number of recruits
       temp = beta0i + betati*log(rectime[j]) + betaui*log(i+1.0);
    // if((numrec[j] <= (i+1))){
        lliki=0.0;
   //   if(((i+1) <= maxc)|(numrec[j]<maxc)){
        if(numrec[j]<maxc){
          lliki += dpois(numrec[j],exp(temp),give_log1);
        }else{
	  lliki += log(1.0-ppois(maxc-1.0,exp(temp),give_log0,give_log0));
        }
        if(srd[j]>=0){
//        Use WP for localized
          memmui = exp(lmemmui)*(i+1.);
          rnb=memmui/(alpha-1.);
          pd2[0]= exp(-fabs(memmui-1.)/sqrt(memnui));
          pis=pd2[0];
          for (k=1; k<(10*Ki); k++){
            pd2[k]= pd2[k-1]*(k+rnb)*pnb*exp((fabs(k-memmui)-fabs(k+1-memmui))/sqrt(memnui))/((double)(k+1));
            pis+=pd2[k];
          }
          for (k=0; k<(10*Ki); k++){
            pd2[k]/=pis;
          }
          pis2=0.;
          for (k=Ki; k<(10*Ki); k++){
            pis2+=pd2[k];
          }
          if(srd[j] <= 10*Ki){
            lliki += log(pd2[srd[j]-1]);
          }else{
            lliki += log(pis2);
          }
        }
        if( dis[j]==1 ){
          pd[i]=p1i[i]*exp(lliki)*(i+1.);
	}else{
          pd[i]=p0i[i]*exp(lliki)*(i+1.);
	}
      }
      pis=0.;
      for (i=0; i<Ki; i++){
        pis+=pd[i];
      }
      for (i=0; i<Ki; i++){
        pd[i]/=pis;
      }
      for (i=1; i<Ki; i++){
       pd[i]=pd[i-1]+pd[i];
      }
      /* Draw unit size for the observed degree */
      /* Now propose the true size for unit i based on reported size and disease status */
      /* In the next three lines a sizei is chosen */
      temp = pd[Ki-1] * unif_rand();
      for (sizei=1; sizei<=Ki; sizei++){
        if(temp <= pd[sizei-1]) break;
      }
      if( dis[j]==1 ){
        nk1[sizei-1]=nk1[sizei-1]+1;
      }else{
        nk0[sizei-1]=nk0[sizei-1]+1;
      }
      u[j]=sizei;

    }
     } 

     /* Deal with the outliers */
     if( dis[j]==1 ){
       umax=nk1[Ki-1];
     }else{
       umax=nk0[Ki-1];
     }
     sizei=Ki;
     for (j=0; j<ni; j++){
      if(srd[j] > 10*Ki){
       while((umax==0) & (sizei > 1)){
         sizei--;
         if( dis[j]==1 ){
           umax=nk1[sizei-1];
         }else{
           umax=nk0[sizei-1];
         }
       }
       u[j]=sizei;
       umax--;
      }
     }
     for (j=0; j<ni; j++){
      if(srd[j] > 10*Ki){
       if( dis[j]==1 ){
        nk1[u[j]-1]=nk1[u[j]-1]+1;
       }else{
        nk0[u[j]-1]=nk0[u[j]-1]+1;
       }
      }
     }

     // Rebuild b
     b[ni-1]=u[ni-1];
     for (i=(ni-2); i>=0; i--){
      b[i]=b[i+1]+u[i];
     }
     /* End of imputed unit sizes for observed */
    }

    /* Draw phis */
    tU=0;
    for (i=ni; i<Ni; i++){
      tU+=u[i];
    }
    r=0.;
    for (i=0; i<ni; i++){
      r+=exp_rand()/(tU+b[i]);
    }

    /* Draw new N */

    gamma0rt=0.;
    gamma1rt=0.;
    for (i=0; i<Ki; i++){
      gamma0rt+=(exp(-r*(i+1))*p0i[i]);
      gamma1rt+=(exp(-r*(i+1))*p1i[i]);
    }
//// gamma0rt=log(gamma0rt);
//// gamma1rt=log(gamma1rt);
//  gammart=0.;
//  for (i=0; i<Ni; i++){
//    tau = tau0 + 0*tau1 * u[i]; // tau1
//    ptau = exp(tau)/(1.+exp(tau));
//    gammart+=(1.-ptau)*gamma0rt+ptau*gamma1rt;
//  }
//  gammart=log(gammart / Ni);
    //
    ptau=exp(tau0)/(1.+exp(tau0));
    gammart=log((1.-ptau)*gamma0rt+ptau*gamma1rt);

// Rprintf("gammart %f orig %f \n", gammart, log((1.-0.2)*gamma0rt+0.2*gamma1rt));

    temp = -100000000.0;
    // N = m + n
    // Compute (log) P(m | \theta and data and \Psi)
    for (i=0; i<imaxm; i++){
      lpm[i]=i*gammart+lgamma(ni+i+1.)-lgamma(i+1.);
//    Add in the (log) prior on m: P(m)
      lpm[i]+=lpriorm[i];
      if(lpm[i] > temp) temp = lpm[i];
    }
    for (i=0; i<imaxm; i++){
      lpm[i]=exp(lpm[i]-temp);
    }
    for (i=1; i<imaxm; i++){
      lpm[i]=lpm[i-1]+lpm[i];
    }
    temp = lpm[imaxm-1] * unif_rand();
    for (Ni=0; Ni<imaxm; Ni++){
      if(temp <= lpm[Ni]) break;
    }
    // Add back the sample size
    Ni += ni;
    if(Ni > imaxN) Ni = imaxN;

    /* Draw unseen sizes */
    for (i=0; i<Ki; i++){
      Nk0[i]=nk0[i];
      Nk1[i]=nk1[i];
    }
    // Set up p0i and p1i to be cumulative for random draws
    for (i=1; i<Ki; i++){
      p0i[i]=p0i[i-1]+p0i[i];
      p1i[i]=p1i[i-1]+p1i[i];
    }
    for (i=ni; i<Ni; i++){
      /* Propose unseen size for unit i */
      /* Use rejection sampling */
      sizei=1000000;
      while(sizei >= Ki){
       sizei=1000000;
       while(log(1.0-unif_rand()) > -r*sizei){
        /* First propose unseen disease status for unit i */
//      tau = tau0 + 0*tau1 * u[i];
//      ptau = exp(tau)/(1.+exp(tau));
        if(unif_rand() < ptau){
          dis[i]=1;
          /* Now propose unseen size for unit i based on disease status */
          /* In the next two lines a sizei is chosen */
          /* with parameters lnlam1i and nu1i */
          temp = unif_rand();
//    for (sizei=1; sizei<=Ki; sizei++){
// Rprintf("i %d p1i %f \n", sizei, p1i[sizei]);
// }
          for (sizei=1; sizei<=Ki; sizei++){
            if(temp <= p1i[sizei-1]) break;
          }
//if(sizei > 33){ Rprintf("i %d u[i] %d p1i %f Ni %d Ki %d\n", i, sizei, p1i[sizei-1], Ni, Ki);}
        }else{
          dis[i]=0;
          /* Now propose unseen size for unit i based on non-disease status */
          /* In the next two lines a sizei is chosen */
          /* with parameters lnlam0i and nu0i */
          temp = unif_rand();
          for (sizei=1; sizei<=Ki; sizei++){
            if(temp <= p0i[sizei-1]) break;
          }
        }
       }
//if(sizei > 34){ Rprintf("i %d dis[i] %d u[i] %d p0i %f p1i %f Ni %d Ki %d\n", i, dis[i], sizei, p0i[sizei-1], p1i[sizei-1], Ni, Ki);}
      }
      u[i]=sizei; // This sets the unit size for this (unobserved) unit
      if(dis[i]==1){
        Nk1[sizei-1]=Nk1[sizei-1]+1;
      }else{
        Nk0[sizei-1]=Nk0[sizei-1]+1;
      }
    }
    discount=discountn;
    for (i=ni; i<Ni; i++){
      discount+=dis[i];
    }

    if (step > 0 && step % iinterval == 0) { 
      /* record statistics for posterity */
      Nd=(double)Ni;
      sample[isamp*dimsample  ]=Nd;
      sample[isamp*dimsample+1]=mu0i;
      sample[isamp*dimsample+2]=mu1i;
      sample[isamp*dimsample+3]=sigma0i;
      sample[isamp*dimsample+4]=sigma1i;
      sample[isamp*dimsample+5]=(double)(Nk0[0]+Nk1[0]);
      sample[isamp*dimsample+6]=tau0;
      sample[isamp*dimsample+7]=tau1;
      temp=0.0;
      for (i=0; i<Ki; i++){
        temp+=(i+1.0)*Nk0[i];
      }
      sample[isamp*dimsample+8]=temp;
      temp=0.0;
      for (i=0; i<Ki; i++){
        temp+=(i+1.0)*Nk1[i];
      }
      sample[isamp*dimsample+9]=temp;
      sample[isamp*dimsample+10]=beta0i;
      sample[isamp*dimsample+11]=betati;
      sample[isamp*dimsample+12]=betaui;
 if(betati < 0.0) Rprintf("beta0 %f betati %f betaui %f\n", beta0i, betati, betaui);
      sample[isamp*dimsample+13]=lmemmui;
      sample[isamp*dimsample+14]=memnui;
      sample[isamp*dimsample+15]=(double)(discount);
      for (i=0; i<Np0; i++){
        sample[isamp*dimsample+16+i]=pdeg0i[i];
      }
      for (i=0; i<Np1; i++){
        sample[isamp*dimsample+16+Np0+i]=pdeg1i[i];
      }
      for (i=0; i<Ki; i++){
        Nk0pos[i]=Nk0pos[i]+Nk0[i];
        Nk1pos[i]=Nk1pos[i]+Nk1[i];
        pos0u[i]+=((Nk0[i]*1.)/Nd);
        pos1u[i]+=((Nk1[i]*1.)/Nd);
      }
      for (i=0; i<ni; i++){
//Rprintf("i %d dis[i] %d u[i]\n", i, dis[i]);
        vsample[isamp*ni+i]=u[i];
if(u[i] > 35){ Rprintf("i %d dis[i] %d u[i] %d p0i %f p1i %f Ni %d Ki %d\n", i, dis[i], u[i], p0i[u[i]-1], p1i[u[i]-1], Ni, Ki);}
        if((srd[i]>0) && (srd[i] <= 10*Ki)){
          if(dis[i]==1){
       	    pos1d[srd[i]-1]+=(1./Nd);
	  }else{
       	    pos0d[srd[i]-1]+=(1./Nd);
	  }
       	}
      }
//    Record the predicted degrees (not unit sizes)
      for (i=ni; i<Ni; i++){
          memmui = exp(lmemmui)*u[i];
          rnb=memmui/(alpha-1.);
          pd[0]= exp(-fabs(memmui-1.)/sqrt(memnui));
          pis=pd[0];
          for (k=1; k<Ki; k++){
            pd[k]= pd[k-1]*(k+rnb)*pnb*exp((fabs(k-memmui)-fabs(k+1-memmui))/sqrt(memnui))/((double)(k+1));
            pis+=pd[k];
          }
          for (k=0; k<Ki; k++){
            pd[k]/=pis;
            if(dis[i]==1){
              pos1d[k]+=(pd[k]/Nd);
            }else{
              pos0d[k]+=(pd[k]/Nd);
            }
          }
      }
      isamp++;
      if (*verbose && isamplesize % isamp == 0 ) Rprintf("Taken %d samples...\n", isamp);
    }
    step++;
  }
  dsamp=((double)isamp);
  for (i=0; i<Ki; i++){
    nk0[i]=Nk0pos[i];
    nk1[i]=Nk1pos[i];
    pos0u[i]/=dsamp;
    pos0d[i]/=dsamp;
    pos1u[i]/=dsamp;
    pos1d[i]/=dsamp;
  }
  for (i=0; i<ni; i++){
     pop[i]=u[i];
  }
  PutRNGstate();  /* Disable RNG before returning */
  free(p0i);
  free(p1i);
  free(pd);
  free(pd2);
  free(u);
  free(b);
  free(nk0);
  free(nk1);
  free(Nk0);
  free(Nk1);
  free(Nk0pos);
  free(Nk1pos);
  free(lpm);
  free(pdeg0i);
  free(pdeg1i);
  free(psample0);
  free(psample1);
  free(lnlamsample0);
  free(lnlamsample1);
  free(nusample0);
  free(nusample1);
  free(beta0sample);
  free(betatsample);
  free(betausample);
  free(lmemmusample);
  free(memnusample);
  free(tau0sample);
  free(tau1sample);
}

void MHwpmemdisease (// int *dis,
	    int *u, int *n, int *K, int *N, int *idiscount,
            double *beta0, double *beta0sd, double *betat, double *betatsd, 
            double *betau, double *betausd, 
            double *lmemmu,
            double *memdfmu,
            double *memnu,
            double *memdfnu,
            int *srd, 
            int *numrec, 
            double *rectime,
            int *maxcoupons,
            double *beta0proposal, double *betatproposal, double *betauproposal, 
            double *tauproposal, 
            double *lmemmuproposal, double *memnuproposal, 
            double *beta0sample, double *betatsample, double *betausample,
            double *lmemmusample,
            double *memnusample,
            double *tau0sample, double *tau1sample,
            int *samplesize, int *staken, int *warmup, int *interval,
            int *verbose
         ) {
  int Ki, maxc, ni, Ni;
  int step, taken, give_log1=1, give_log0=0;
  int i, k, isamp, iinterval, isamplesize, iwarmup;
  int discount;
  double ip, cutoff;
  double temp;
  double beta0star, betatstar, betaustar;
  double beta0i, betati, betaui;
  double qi, qstar, lliki, llikstar;
  double taustar, ptaustar, ptau, taui, tau0i, tau1i;
  double ptau0star, ptau1star, ptau0, ptau1;
  double tau0star, tau1star;
  double lmemmustar, memmustar, memmui, lmemmui;
  double memnui, memnustar;
  double rmemnui, rmemnustar;
  double pibeta0star, pibeta0i;
  double pibetatstar=0.0, pibetati=0.0;
  double pibetaustar=0.0, pibetaui=0.0;
  double pimemstar, pimemi;
  double dbeta0, dbeta0sd, dbetat, dbetatsd, dbetau, dbetausd;
  double dmemdfmu, dmemdfnu, rmemdfmu;
  double dlmemmu;
  double dmemnu;
  double dbeta0proposal, dbetatproposal, dbetauproposal;
  double dtauproposal;
  double dlmemmuproposal, dmemnuproposal;
  double pis, pis2;
  double alpha=25., pnb, rnb;

  Ki=(*K);
  double *pd = (double *) malloc(sizeof(double) * (10*Ki));
  pnb=(alpha-1.)/alpha;

//GetRNGstate();  /* R function enabling uniform RNG */

  Ni=(*N);
  isamplesize=(*samplesize);
  iinterval=(*interval);
  iwarmup=(*warmup);
 //Rprintf("Started MCMC %d %d %d\n", isamplesize, iwarmup, iinterval);
  dbeta0=(*beta0);
  dbeta0sd=(*beta0sd);
  dbetat=(*betat);
  dbetatsd=(*betatsd);
  dbetau=(*betau);
  dbetausd=(*betausd);
  discount=(*idiscount);
  dlmemmu=(*lmemmu);
  dmemnu=(*memnu);
  dmemdfmu=(*memdfmu);
  rmemdfmu=sqrt(dmemdfmu);
  dmemdfnu=(*memdfnu);
  dbeta0proposal=(*beta0proposal);
  dbetatproposal=(*betatproposal);
  dbetauproposal=(*betauproposal);
  dtauproposal=(*tauproposal);
  dlmemmuproposal=(*lmemmuproposal);
  dmemnuproposal=(*memnuproposal);

  // First set starting values
  isamp = taken = 0;
  step = -iwarmup;
  tau0i = tau0sample[0];
  tau1i = tau1sample[0];
  ni =(*n);
  maxc=(*maxcoupons);
  beta0i = beta0sample[0];
  betati = betatsample[0];
  betaui = betausample[0];
  lmemmui = lmemmusample[0];
  memnui = memnusample[0];
  rmemnui = sqrt(memnui);

  // Compute initial current lik
  lliki = 0.0;
  for (i=0; i<ni; i++){
     temp = beta0i + betati*log(rectime[i]) + betaui*log(u[i]);
 // if(numrec[i] <= u[i]){
 //  if((u[i] <= maxc)|(numrec[i]<maxc)){
     if(numrec[i]<maxc){
       lliki += dpois(numrec[i],exp(temp),give_log1);
     }else{
       lliki += log(1.0-ppois(maxc-1.0,exp(temp),give_log0,give_log0));
     }
     if(srd[i]>=0){
//    Use WP for localized
      memmui = exp(lmemmui)*u[i];
      rnb=memmui/(alpha-1.);
      pd[0]= memmui*exp(-fabs(memmui-1.)/sqrt(memnui));
      pis=pd[0];
      for (k=1; k<(10*Ki); k++){
        pd[k]= pd[k-1]*(k+rnb)*pnb*exp((fabs(k-memmui)-fabs(k+1-memmui))/sqrt(memnui))/((double)(k+1));
        pis+=pd[k];
      }
      for (k=0; k<(10*Ki); k++){
        pd[k]/=pis;
      }
      pis2=0.;
      for (k=Ki; k<(10*Ki); k++){
        pis2+=pd[k];
      }
      if(srd[i] <= 10*Ki){
        lliki += log(pd[srd[i]-1]);
      }else{
        lliki += log(pis2);
      }
      lliki += log((double)(u[i]));
     }
 // }
  }
  if(!isfinite(lliki)) lliki = -100000.0; 

  // Compute initial prior
  pibeta0i = dnorm(beta0i, dbeta0, dbeta0sd, give_log1);
  if(dbetatsd > 0.0) pibetati = dnorm(betati, dbetat, dbetatsd, give_log1);
  if(dbetausd > 0.0) pibetaui = dnorm(betaui, dbetau, dbetausd, give_log1);
  pimemi = dnorm(lmemmui, dlmemmu, rmemnui/rmemdfmu, give_log1);
  pimemi = pimemi+dsclinvchisq(memnui, dmemdfnu, dmemnu);

// Rprintf("Started MCMC %d %d %f\n", isamp, iwarmup, step);
  // Now do the MCMC updates (starting with the warmup updates)
  while (isamp < isamplesize && step < iwarmup) {
    /* Start with the disease status parameters */
    tau0star = rnorm(tau0i, dtauproposal);
    tau1star = rnorm(tau1i, 0.1*dtauproposal);
    ptau0star = exp(tau0star)/(1.+exp(tau0star));
    ptau1star = exp(tau1star)/(1.+exp(tau1star));
    /* Propose new beta */
    beta0star = rnorm(beta0i, dbeta0proposal);
    if(dbetatsd > 0.0){
      betatstar = rnorm(betati, dbetatproposal);
    }else{
      betatstar = betati;
    }
    if(dbetausd > 0.0){
 //Rprintf("betaui %f dbetausd %f dbetauproposal %f\n", betaui, dbetausd, dbetauproposal);
      betaustar = rnorm(betaui, dbetauproposal);
    }else{
      betaustar = betaui;
    }
    /* Propose new memnu and lmemmu */
    lmemmustar = rnorm(lmemmui, dlmemmuproposal);
// VIP Remember this next line hold the optimism fixed at 1!!! VIP
    lmemmustar = lmemmui;

//  lmemmustar = 0.0;
//  rmemnustar = rnorm(memnui, dmemnuproposal);
    memnustar = memnui*exp(rnorm(0., dmemnuproposal));
    rmemnustar = sqrt(memnustar);

    llikstar = 0.0;
    for (i=0; i<ni; i++){
  //  if(numrec[i] <= u[i]){
       temp = beta0star + betatstar*log(rectime[i]) + betaustar*log(u[i]);
  //   if((u[i] <= maxc)|(numrec[i]<maxc)){
       if(numrec[i]<maxc){
	llikstar += dpois(numrec[i],exp(temp),give_log1);
       }else{
	llikstar += log(1.0-ppois(maxc-1.0,exp(temp),give_log0,give_log0));
       }
       if(srd[i]>=0){
        memmustar = exp(lmemmustar)*u[i];
        rnb=memmustar/(alpha-1.);
        pd[0]= exp(-fabs(memmustar-1.)/sqrt(memnustar));
        pis=pd[0];
        for (k=1; k<(10*Ki); k++){
          pd[k]= pd[k-1]*(k+rnb)*pnb*exp((fabs(k-memmustar)-fabs(k+1-memmustar))/sqrt(memnustar))/((double)(k+1));
          pis+=pd[k];
        }
        for (k=0; k<(10*Ki); k++){
          pd[k]/=pis;
        }
        pis2=0.;
        for (k=Ki; k<(10*Ki); k++){
          pis2+=pd[k];
        }
        if(srd[i] <= 10*Ki){
          llikstar += log(pd[srd[i]-1]);
        }else{
          llikstar += log(pis2);
        }
        llikstar += log((double)(u[i]));
       }
  //  }
    }
    if(!isfinite(llikstar)) llikstar = -100000.0; 

    /* Calculate pieces of the prior. */
    pibeta0star = dnorm(beta0star, dbeta0, dbeta0sd, give_log1);
    if(dbetatsd > 0.0) pibetatstar = dnorm(betatstar, dbetat, dbetatsd, give_log1);
    if(dbetausd > 0.0) pibetaustar = dnorm(betaustar, dbetau, dbetausd, give_log1);
    pimemstar = dnorm(lmemmustar, dlmemmu, rmemnustar/rmemdfmu, give_log1);
    pimemstar = pimemstar+dsclinvchisq(memnustar, dmemdfnu, dmemnu);

    qi = dnorm(log(memnui/memnustar)/dmemnuproposal,0.,1.,give_log1)
         -log(dmemnuproposal*memnui);

    qstar = dnorm(log(memnustar/memnui)/dmemnuproposal,0.,1.,give_log1)
                  -log(dmemnuproposal*memnustar);

    /* Calculate ratio */
    ip =      pibeta0star-pibeta0i;
    if(dbetatsd > 0.0) ip = ip + pibetatstar-pibetati;
    if(dbetausd > 0.0) ip = ip + pibetaustar-pibetaui;

    ip = ip + pimemstar - pimemi;

    /* Add the disease status */
//  for (i=0; i<Ni; i++){
//    taustar = tau0star + tau1star * u[i];
 //   ptaustar = exp(taustar)/(1.+exp(taustar));
  //  if( dis[i]==1 ){
 //     ip+=log(ptaustar);
 //   }else{
  //    ip+=log(1.-ptaustar);
//    }
 //   taui = tau0i + tau1i * u[i];
  //  ptau = exp(taui)/(1.+exp(taui));
   // if( dis[i]==1 ){
 //     ip-=log(ptau);
  //  }else{
   //   ip-=log(1.-ptau);
    //}
//  }
    ip+=(discount*log(ptau0star)+(Ni-discount)*log(1.-ptau0star));
    ptau0 = exp(tau0i)/(1.+exp(tau0i));
    ip-=(discount*log(ptau0)+(Ni-discount)*log(1.-ptau0));

    /* The logic is to set exp(cutoff) = exp(ip) * qratio ,
    then let the MH probability equal min{exp(cutoff), 1.0}.
    But we'll do it in log space instead.  */
    cutoff = ip + llikstar - lliki + qi - qstar;
// if(betatstar < 0.0) Rprintf("cutoff %f betatstar %f pibetatstar-pibetati %f\n", beta0i, betatstar, pibetatstar-pibetati);
      
    /* if we accept the proposed values */
    if (cutoff >= 0.0 || log(unif_rand()) < cutoff) { 
      /* Make proposed changes */
      tau0i = tau0star;
      tau1i = tau1star;
      beta0i = beta0star;
      betati = betatstar;
// if(betati < 0.0) Rprintf("accepted cutoff %f betatstar %f pibetatstar-pibetati %f\n", beta0i, betatstar, pibetatstar-pibetati);
      betaui = betaustar;
      lmemmui = lmemmustar;
      memnui = memnustar;
      rmemnui = rmemnustar;
      lliki = llikstar;
      qi = qstar;
      pibeta0i = pibeta0star;
      if(dbetatsd > 0.0) pibetati = pibetatstar;
      if(dbetausd > 0.0) pibetaui = pibetaustar;
      pimemi = pimemstar;
      taken++;
      if (step > 0 && step % iinterval == 0) { 
        /* record statistics for posterity */
        tau0sample[isamp] = tau0i;
        tau1sample[isamp] = tau1i;
        beta0sample[isamp]=beta0i;
        betatsample[isamp]=betati;
        betausample[isamp]=betaui;
        lmemmusample[isamp]=lmemmui;
        memnusample[isamp]=memnui;
        isamp++;
        if (*verbose && isamplesize % isamp == 0) Rprintf("Taken %d MH samples...\n", isamp);
      }
    }
    step++;
  }
//PutRNGstate();  /* Disable RNG before returning */
  free(pd);
  /*Check for interrupts (if recursion is taking way too long...)*/
  R_CheckUserInterrupt();
  *staken = taken;
}

void MHcmpthetawpdisease (int *dis, int *u, int *Nk0, int *Nk1, int *K, int *idiscount,
            double *mu0, double *mu1, double *dfmu, 
            double *sigma0, double *sigma1, double *dfsigma,
            double *lnlamproposal, 
            double *nuproposal, 
            double *tauproposal, 
            int *N, int *Np0i, int *Np1i,
	    double *psample0, double *psample1,
            double *lnlamsample0, double *nusample0,
            double *lnlamsample1, double *nusample1,
            double *tau0sample, double *tau1sample,
            int *samplesize, int *staken, int *warmuptheta, int *interval,
            int *verbose
         ) {
  int Np0, Np1;
  int step, taken, give_log1=1, give_log0=0;
  int i, Ki, Ni, isamp, iinterval, isamplesize, iwarmuptheta;
  int discount;
  double ip, cutoff;
  double mu0i, mu0star, lnlam0star, lnlam0i, lp;
  double mu1i, mu1star, lnlam1star, lnlam1i;
  double p0is, p0stars;
  double p1is, p1stars;
  double sigma0star, sigma0i, sigma20star, sigma20i, qnu0star, qnu0i;
  double sigma1star, sigma1i, sigma21star, sigma21i, qnu1star, qnu1i;
  double nu0star, nu1star, nu0i, nu1i;
  double taustar, ptaustar, ptau, taui;
  double tau0star, tau0i, tau1star, tau1i;
  double p0ithetastar, p0ithetai, p1ithetastar, p1ithetai;
  double ddfmu, rdfmu, ddfsigma;
  double dmu0, dmu1;
  double dsigma0, dsigma1, dsigma20, dsigma21;
  double dlnlamproposal, dnuproposal;
  double dtauproposal;
  double errval=0.0000000001, lzcmp;
  double tmp1, tmp2;

//GetRNGstate();  /* R function enabling uniform RNG */

  Ki=(*K);
  Ni=(*N);
  Np0=(*Np0i);
  Np1=(*Np1i);
  double *p0star = (double *) malloc(sizeof(double) * Ki);
  double *p0i = (double *) malloc(sizeof(double) * Ki);
  double *odeg0star = (double *) malloc(sizeof(double) * Np0);
  double *odeg0i = (double *) malloc(sizeof(double) * Np0);
  double *pdeg0star = (double *) malloc(sizeof(double) * Np0);
  double *pdeg0i = (double *) malloc(sizeof(double) * Np0);
  double *p1star = (double *) malloc(sizeof(double) * Ki);
  double *p1i = (double *) malloc(sizeof(double) * Ki);
  double *odeg1star = (double *) malloc(sizeof(double) * Np1);
  double *odeg1i = (double *) malloc(sizeof(double) * Np1);
  double *pdeg1star = (double *) malloc(sizeof(double) * Np1);
  double *pdeg1i = (double *) malloc(sizeof(double) * Np1);

  isamplesize=(*samplesize);
  iinterval=(*interval);
  iwarmuptheta=(*warmuptheta);
  ddfmu=(*dfmu);
  rdfmu=sqrt(ddfmu);
  ddfsigma=(*dfsigma);
  discount=(*idiscount);
  dsigma0=(*sigma0);
  dsigma1=(*sigma1);
  dsigma20=(dsigma0*dsigma0);
  dsigma21=(dsigma1*dsigma1);
  dmu0=(*mu0);
  dmu1=(*mu1);
  dnuproposal=(*nuproposal);
  dlnlamproposal=(*lnlamproposal);
  dtauproposal=(*tauproposal);

  // First set starting values
  isamp = taken = 0;
  step = -iwarmuptheta;
  tau0i = tau0sample[0];
  tau1i = tau1sample[0];
  p0is=1.;
  for (i=0; i<Np0; i++){
    pdeg0i[i] = psample0[i];
    p0is-=pdeg0i[i];
  }
  p1is=1.;
  for (i=0; i<Np1; i++){
    pdeg1i[i] = psample1[i];
    p1is-=pdeg1i[i];
  }
  for (i=0; i<Np0; i++){
    odeg0i[i] = log(pdeg0i[i]/p0is);
  }
  for (i=0; i<Np1; i++){
    odeg1i[i] = log(pdeg1i[i]/p1is);
  }
  lnlam0i = lnlamsample0[0];
  if(rdfmu <= 0.0){
    lnlam0star = lnlam0i;
  }
  lnlam1i = lnlamsample1[0];
  if(rdfmu <= 0.0){
    lnlam1star = lnlam1i;
  }
  nu0i = nusample0[0];
  nu1i = nusample1[0];
  //
  p1is=0.;
  lzcmp = zcmp(exp(lnlam1i), nu1i, errval, 2*Ki, give_log1);
  p1i[Np1]=cmp(Np1+1,lnlam1i,nu1i,lzcmp,give_log0);
  p1is+=p1i[Np1];
  for (i=Np1+1; i<Ki; i++){
    p1i[i]=p1i[i-1]*exp(lnlam1i-nu1i*log((double)(i+1)));
    p1is+=p1i[i];
  }
  for (i=0; i<Ki; i++){
    p1i[i]/=p1is;
  }
  p1is=1.;
  for (i=0; i<Np1; i++){
    p1is-=pdeg1i[i];
  }
  for (i=0; i<Ki; i++){
    p1i[i]=p1i[i]*p1is;
  }
  for (i=0; i<Np1; i++){
    p1i[i]=pdeg1i[i];
  }
  // Bin last group
  p1is=1.;
  for (i=0; i<(Ki-1); i++){
    p1is-=p1i[i];
  }
  p1i[Ki-1]=p1is;
  //
  p0is=0.;
  lzcmp = zcmp(exp(lnlam0i), nu0i, errval, 2*Ki, give_log1);
  p0i[Np0]=cmp(Np0+1,lnlam0i,nu0i,lzcmp,give_log0);
  p0is+=p0i[Np0];
  for (i=Np0+1; i<Ki; i++){
    p0i[i]=p0i[i-1]*exp(lnlam0i-nu0i*log((double)(i+1)));
    p0is+=p0i[i];
  }
  for (i=0; i<Ki; i++){
    p0i[i]/=p0is;
  }
  p0is=1.;
  for (i=0; i<Np0; i++){
    p0is-=pdeg0i[i];
  }
  for (i=0; i<Ki; i++){
    p0i[i]=p0i[i]*p0is;
  }
  for (i=0; i<Np0; i++){
    p0i[i]=pdeg0i[i];
  }
  // Bin last group
  p0is=1.;
  for (i=0; i<(Ki-1); i++){
    p0is-=p0i[i];
  }
  p0i[Ki-1]=p0is;

  // Now computes mean and s.d. from log-lambda0 and nu0
  mu0i=0.0;
  sigma20i=0.0;
  for (i=0; i<Ki; i++){
    mu0i+=p0i[i]*(i+1);
    sigma20i+=p0i[i]*(i+1)*(i+1);
  }
  sigma20i=sigma20i-mu0i*mu0i;
  sigma0i  = sqrt(sigma20i);

  p0ithetai = dsclinvchisq(sigma20i, ddfsigma, dsigma20);
  if(rdfmu > 0.0){
   p0ithetai = p0ithetai + dnorm(mu0i, dmu0, sigma0i/rdfmu, give_log1);
  }

  // Now computes mean and s.d. from log-lambda1 and nu1
  mu1i=0.0;
  sigma21i=0.0;
  for (i=0; i<Ki; i++){
    mu1i+=p1i[i]*(i+1);
    sigma21i+=p1i[i]*(i+1)*(i+1);
  }
  sigma21i=sigma21i-mu1i*mu1i;
  sigma1i  = sqrt(sigma21i);

  p1ithetai = dsclinvchisq(sigma21i, ddfsigma, dsigma21);
  if(rdfmu > 0.0){
   p1ithetai = p1ithetai + dnorm(mu1i, dmu1, sigma1i/rdfmu, give_log1);
  }

  // Now do the MCMC updates (starting with the warmup updates)
  while (isamp < isamplesize) {
    /* Propose new theta */

    /* Start with the disease status parameters */
    tau0star = rnorm(tau0i, dtauproposal);
    tau1star = rnorm(tau1i, 0.01*dtauproposal);

    /* Now the degree distribution model parameters */
    for (i=0; i<Np0; i++){
      odeg0star[i] = rnorm(odeg0i[i], dlnlamproposal);
    }
    /* Convert from odds to probabilities */
    p0is=1.;
    for (i=0; i<Np0; i++){
      pdeg0star[i] = exp(odeg0star[i]);
      p0is+=pdeg0star[i];
    }
    for (i=0; i<Np0; i++){
      pdeg0star[i]/=p0is;
    }
    /* Now the degree distribution (log) mean and s.d. parameters */
    if(rdfmu > 0.0){
     lnlam0star = rnorm(lnlam0i, dlnlamproposal);
    }
    nu0star = nu0i*exp(rnorm(0., dnuproposal));

    /* Now the degree distribution model parameters */
    for (i=0; i<Np1; i++){
      odeg1star[i] = rnorm(odeg1i[i], dlnlamproposal);
    }
    /* Convert from odds to probabilities */
    p1is=1.;
    for (i=0; i<Np1; i++){
      pdeg1star[i] = exp(odeg1star[i]);
      p1is+=pdeg1star[i];
    }
    for (i=0; i<Np1; i++){
      pdeg1star[i]/=p1is;
    }
    /* Now the degree distribution (log) mean and s.d. parameters */
    if(rdfmu > 0.0){
     lnlam1star = rnorm(lnlam1i, dlnlamproposal);
    }
    nu1star = nu1i*exp(rnorm(0., dnuproposal));

    /* Check for magnitude */

    p0stars=0.;
    lzcmp = zcmp(exp(lnlam0star), nu0star, errval, 2*Ki, give_log1);
    p0star[Np0]=cmp(Np0+1,lnlam0star,nu0star,lzcmp,give_log0);
    p0stars+=p0star[Np0];
    for (i=Np0+1; i<Ki; i++){
      p0star[i]=p0star[i-1]*exp(lnlam0star-nu0star*log((double)(i+1)));
      p0stars+=p0star[i];
    }
    for (i=0; i<Ki; i++){
      p0star[i]/=p0stars;
    }
    p0stars=1.;
    for (i=0; i<Np0; i++){
      p0stars-=pdeg0star[i];
    }
    for (i=Np0; i<Ki; i++){
      p0star[i]*=p0stars;
    }
    for (i=0; i<Np0; i++){
      p0star[i]=pdeg0star[i];
    }
    // Bin last group
    p0stars=1.;
    for (i=0; i<(Ki-1); i++){
      p0stars-=p0star[i];
    }
    p0star[Ki-1]=p0stars;

    p1stars=0.;
    lzcmp = zcmp(exp(lnlam1star), nu1star, errval, 2*Ki, give_log1);
    p1star[Np1]=cmp(Np1+1,lnlam1star,nu1star,lzcmp,give_log0);
    p1stars+=p1star[Np1];
    for (i=Np1+1; i<Ki; i++){
      p1star[i]=p1star[i-1]*exp(lnlam1star-nu1star*log((double)(i+1)));
      p1stars+=p1star[i];
    }
    for (i=0; i<Ki; i++){
      p1star[i]/=p1stars;
    }
    p1stars=1.;
    for (i=0; i<Np1; i++){
      p1stars-=pdeg1star[i];
    }
    for (i=Np1; i<Ki; i++){
      p1star[i]*=p1stars;
    }
    for (i=0; i<Np1; i++){
      p1star[i]=pdeg1star[i];
    }
    // Bin last group
    p1stars=1.;
    for (i=0; i<(Ki-1); i++){
      p1stars-=p1star[i];
    }
    p1star[Ki-1]=p1stars;

    // Now compute mean and s.d. from log-lambda and nu
    mu0star=0.0;
    sigma20star=0.0;
    for (i=0; i<Ki; i++){
      mu0star+=p0star[i]*(i+1);
      sigma20star+=p0star[i]*(i+1)*(i+1);
    }
    sigma20star=sigma20star-mu0star*mu0star;
    sigma0star  = sqrt(sigma20star);

    mu1star=0.0;
    sigma21star=0.0;
    for (i=0; i<Ki; i++){
      mu1star+=p1star[i]*(i+1);
      sigma21star+=p1star[i]*(i+1)*(i+1);
    }
    sigma21star=sigma21star-mu1star*mu1star;
    sigma1star  = sqrt(sigma21star);

    /* Calculate pieces of the posterior. */
    qnu0star = dnorm(log(nu0star/nu0i)/dnuproposal,0.,1.,give_log1)
                  -log(dnuproposal*nu0star);
    p0ithetastar = dsclinvchisq(sigma20star, ddfsigma, dsigma20);
    if(rdfmu > 0.0){
     p0ithetastar = p0ithetastar + dnorm(mu0star, dmu0, sigma0star/rdfmu, give_log1);
    }
    qnu0i = dnorm(log(nu0i/nu0star)/dnuproposal,0.,1.,give_log1)
               -log(dnuproposal*nu0i);

    qnu1star = dnorm(log(nu1star/nu1i)/dnuproposal,0.,1.,give_log1)
                  -log(dnuproposal*nu1star);
    p1ithetastar = dsclinvchisq(sigma21star, ddfsigma, dsigma21);
    if(rdfmu > 0.0){
     p1ithetastar = p1ithetastar + dnorm(mu1star, dmu1, sigma1star/rdfmu, give_log1);
    }
    qnu1i = dnorm(log(nu1i/nu1star)/dnuproposal,0.,1.,give_log1)
               -log(dnuproposal*nu1i);

    /* Calculate ratio */
    ip  = p0ithetastar-p0ithetai;
    ip += p1ithetastar-p1ithetai;

    /* Add the disease status */
//  tmp1 = ip;
//  for (i=0; i<Ni; i++){
//    taustar = tau0star + 0 * tau1star * u[i];
//    ptaustar = exp(taustar)/(1.+exp(taustar));
//    if( dis[i]==1 ){
//      ip+=log(ptaustar);
//    }else{
//      ip+=log(1.-ptaustar);
//    }
//  tmp2 = ip;
//    taui = tau0i + 0 * tau1i * u[i];
//    ptau = exp(taui)/(1.+exp(taui));
//    if( dis[i]==1 ){
//      ip-=log(ptau);
//    }else{
//      ip-=log(1.-ptau);
//    }
//  }
    ptaustar = exp(tau0star)/(1.+exp(tau0star));
    ip+=(discount*log(ptaustar)+(Ni-discount)*log(1.-ptaustar));
    ptau = exp(tau0i)/(1.+exp(tau0i));
    ip-=(discount*log(ptau)+(Ni-discount)*log(1.-ptau));

// Rprintf("ip %f ip %f n1 %f n2 %f\n", (discount*log(ptaustar)+(Ni-discount)*log(1.-ptaustar)),
//                          (discount*log(ptau)+(Ni-discount)*log(1.-ptau)), tmp2-tmp1,tmp2-ip );

    for (i=0; i<Ki; i++){
     if(Nk0[i]>0){
      lp = log(p0star[i]/p0i[i]);
      if(fabs(lp) < 100.){ip += (Nk0[i]*lp);}
     }
     if(Nk1[i]>0){
      lp = log(p1star[i]/p1i[i]);
      if(fabs(lp) < 100.){ip += (Nk1[i]*lp);}
     }
    }
    /* The logic is to set exp(cutoff) = exp(ip) * qratio ,
    then let the MH probability equal min{exp(cutoff), 1.0}.
    But we'll do it in log space instead.  */
    cutoff = ip + qnu0i-qnu0star + qnu1i-qnu1star;
      
    /* if we accept the proposed network */
    if (cutoff >= 0.0 || log(unif_rand()) < cutoff) { 
      /* Make proposed changes */
      tau0i = tau0star;
      tau1i = tau1star;
      for (i=0; i<Np0; i++){
        odeg0i[i] = odeg0star[i];
        pdeg0i[i] = pdeg0star[i];
      }
      lnlam0i = lnlam0star;
      nu0i = nu0star;
      qnu0i = qnu0star;
      p0ithetai = p0ithetastar;
      for (i=0; i<Ki; i++){
        p0i[i] = p0star[i];
      }
      for (i=0; i<Np1; i++){
        odeg1i[i] = odeg1star[i];
        pdeg1i[i] = pdeg1star[i];
      }
      lnlam1i = lnlam1star;
      nu1i = nu1star;
      qnu1i = qnu1star;
      p1ithetai = p1ithetastar;
      for (i=0; i<Ki; i++){
        p1i[i] = p1star[i];
      }
      taken++;
      if (step > 0 && step % iinterval == 0) { 
        /* record statistics for posterity */
        tau0sample[isamp] = tau0i;
        tau1sample[isamp] = tau1i;
        lnlamsample0[isamp]=lnlam0i;
        nusample0[isamp]=nu0i;
        for (i=0; i<Np0; i++){
          psample0[i]=pdeg0i[i];
        }
        lnlamsample1[isamp]=lnlam1i;
        nusample1[isamp]=nu1i;
        for (i=0; i<Np1; i++){
          psample1[i]=pdeg1i[i];
        }
        isamp++;
        if (*verbose && isamplesize % isamp == 0 ) Rprintf("Taken %d MH samples...\n", isamp);
      }
    }
    step++;
  }
  free(p0i);
  free(p0star);
  free(odeg0i);
  free(odeg0star);
  free(pdeg0i);
  free(pdeg0star);
  free(p1i);
  free(p1star);
  free(odeg1i);
  free(odeg1star);
  free(pdeg1i);
  free(pdeg1star);
//PutRNGstate();  /* Disable RNG before returning */
  /*Check for interrupts (if recursion is taking way too long...)*/
  R_CheckUserInterrupt();
  *staken = taken;
}
