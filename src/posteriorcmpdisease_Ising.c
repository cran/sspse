/*******************************************************************/
/* Computation of the log-likelihood and marginal posterior of size*/
/*******************************************************************/

#include "posteriorcmpdisease_Ising.h"
#include "cmp.h"
#include <R.h>
#include <Rmath.h>
#include <math.h>

void gcmpdiseasepaired (int *pop, int *dis,
            int *K,
            int *n,
            int *samplesize, int *warmup, int *interval,
            double *mu0, double *mu1, double *dfmu,
            double *sigma0, double *sigma1,
	    double *dfsigma,
            double *lnlam0, double *lnlam1,
            double *nu0, double *nu1,
            int *Np0i, int *Np1i,
            int *srd,
            int *numrec,
            double *rectime,
            int *maxcoupons,
            double *lnlamproposal,
            double *nuproposal,
            double *tauproposal,
            int *N, int *maxN,
            double *sample,
            double *pos0u, double *pos1u,
            double *lpriorm,
            double *logdiseaseprior,
            int *warmuptheta,
            int *verbose
                         ) {
  int dimsample, Np0, Np1;
  int step, staken, getone=1, intervalone=1, verboseMHcmp = 0;
  int i, ni, Ni, Ki, isamp, iinterval, isamplesize, iwarmup;
  double dsamp;
  double mu0i, sigma0i, lnlam0i, nu0i;
  double mu1i, sigma1i, lnlam1i, nu1i;
  double tau, ptau;
  double ptau1, ptau2, ptau3, ptau4;
  double tau1;
  double sigma2i;
  int tU, sizei, imaxN, imaxm, give_log0=0, give_log1=1;
  int discountn, discount, dispairsn, dispairs;
  double r, Nd;
  double gammart, gamma0rt, gamma1rt;
  double p0is, p1is;
  double temp, uprob;
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
  
  dimsample=14+Np0+Np1;

  double *p0i = (double *) malloc(sizeof(double) * Ki);
  double *p1i = (double *) malloc(sizeof(double) * Ki);
  int *u = (int *) malloc(sizeof(int) * imaxN);
  int *b = (int *) malloc(sizeof(int) * ni);
  int *Nk00 = (int *) malloc(sizeof(int) * Ki);
  int *Nk10 = (int *) malloc(sizeof(int) * Ki);
  int *Nk01 = (int *) malloc(sizeof(int) * Ki);
  int *Nk11 = (int *) malloc(sizeof(int) * Ki);
  int *Nk0 = (int *) malloc(sizeof(int) * Ki);
  int *Nk1 = (int *) malloc(sizeof(int) * Ki);
  int *nk00 = (int *) malloc(sizeof(int) * Ki);
  int *nk10 = (int *) malloc(sizeof(int) * Ki);
  int *nk01 = (int *) malloc(sizeof(int) * Ki);
  int *nk11 = (int *) malloc(sizeof(int) * Ki);
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
  double *tausample = (double *) malloc(sizeof(double) * isamplesize);
  double *tau1sample = (double *) malloc(sizeof(double) * isamplesize);

  for (i=0; i<Ki; i++){
    nk0[i]=0;
    nk1[i]=0;
    nk00[i]=0;
    nk10[i]=0;
    nk01[i]=0;
    nk11[i]=0;
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
  for (i=1; i<ni; i++){
    // Create sample counts from the data
    if( dis[i-1]==1 ){
     if( dis[i]==1 ){
      nk11[u[i]-1]=nk11[u[i]-1]+1;
     }else{
      nk10[u[i]-1]=nk10[u[i]-1]+1;
     }
    }else{
     if( dis[i]==1 ){
      nk01[u[i]-1]=nk01[u[i]-1]+1;
     }else{
      nk00[u[i]-1]=nk00[u[i]-1]+1;
     }
    }
  }
  uprob/=ni;
  uprob = 0.5 + uprob/2.0;
  b[ni-1]=u[ni-1];
  for (i=(ni-2); i>=0; i--){
    b[i]=b[i+1]+u[i];
  }
  for (i=0; i<Ki; i++){
     Nk00[i]=nk00[i];
     Nk01[i]=nk01[i];
     Nk0[i]=nk0[i];
     Nk0pos[i]=0;
     pos0u[i]=0.;
     Nk10[i]=nk10[i];
     Nk11[i]=nk11[i];
     Nk1[i]=nk1[i];
     Nk1pos[i]=0;
     pos1u[i]=0.;
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
  dispairsn=0;
  for (i=0; i<ni; i++){
    r+=(exp_rand()/(tU+b[i]));
    discountn+=dis[i];
    if(i > 0) dispairsn+=((dis[i-1]==dis[i]));
  }
  discount=discountn;
  dispairs=dispairsn;
  for (i=ni; i<Ni; i++){
    discount+=dis[i];
    dispairs+=((dis[i-1]==dis[i]));
  }

  tausample[0] = -1.386294;  // logit(0.2)
  tausample[0] = -6.57879;  // logit(0.082)
  tausample[0] = -1.3793;  // logit(0.082)
  tausample[0] = 0.;  // logit(0.082)
  tau1sample[0] = 0.0;  // logit(0.082)

  for (i=0; i<Np0; i++){
     psample0[i] = 0.01;
  }
  for (i=0; i<Np1; i++){
     psample1[i] = 0.01;
  }
  lnlamsample0[0] = (*lnlam0);
  lnlamsample1[0] = (*lnlam1);
  nusample0[0] = (*nu0);
  nusample1[0] = (*nu1);

  isamp = 0;
  step = -iwarmup;
  while (isamp < isamplesize) {

    /* Draw new theta and tau */
    /* but less often than the other full conditionals */
    /*  */
    /* theta = (lnlam, nu))  while tau is the logit(prev) */
    /*  */
    if (step == -iwarmup || step % 10 == 0) { 
// Rprintf("Started %d %f\n", step, lnlamsample0[0]);
     MHcmpthetadiseasepaired(dis, u, Nk00, Nk10, Nk01, Nk11,
       Nk0, Nk1, K,
       mu0,mu1,dfmu,sigma0,sigma1,
       dfsigma,lnlamproposal,nuproposal,tauproposal,
       &Ni, &Np0, &Np1, psample0, psample1,
       lnlamsample0, nusample0,
       lnlamsample1, nusample1,
       tausample, tau1sample,
       logdiseaseprior,
       &getone, &staken, warmuptheta, &intervalone, 
       &verboseMHcmp);
// Rprintf("Ended %d %d\n", step, discount);

 //  Sample 0 is taken as the sampler only draws one sample (as &getone =1)
     lnlam0i=lnlamsample0[0];
     lnlam1i=lnlamsample1[0];
     nu0i=nusample0[0];
     nu1i=nusample1[0];

     tau=tausample[0];
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

    // Now compute mean and s.d. from log-lambda and nu
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
// gamma0rt=log(gamma0rt);
// gamma1rt=log(gamma1rt);
//  gammart=0.;
//  for (i=0; i<Ni; i++){
//    if(i > 0){
//      ptau4 = exp(tau+(dis[i-1]*dis[i])*tau1) / (1.+exp(tau+(dis[i-1]*dis[i])*tau1));
//    }else{
//      ptau4 = exp(tau) / (1.+exp(tau));
//    }
// // ptau = exp(tau)/(1.+exp(tau));
//    gammart+=(1.-ptau4)*gamma0rt+ptau4*gamma1rt;
//  }
//  gammart=log(gammart / Ni);
//  //
//  Rprintf("ptau %f\n", ptau);
    ptau = exp(tau) / (1. + exp(tau));
    ptau4= exp(tau + tau1)  / (1. + exp(tau+tau1));
    ptau2 = 1. / (1. + exp(tau1 - tau));
    ptau1 = ptau4 - ptau2;
    ptau3 = ptau2 / (1 - ptau4 + ptau2);
    ptau = ptau3 + (ptau - ptau3) * (1. - pow(ptau1,(double)Ni)) / (Ni*(1. - ptau1));
//  ptau = 0.2;
    ptau3 = ((double)discount) / ((double)Ni);
//  Rprintf("ptau %f ptau3 %f\n", ptau, ptau3);
//  gammart=(1.-ptau4)*gamma0rt+ptau4*gamma1rt;
    gammart=log((1.-ptau)*gamma0rt+ptau*gamma1rt);
//  
//  for (i=1; i<Ni; i++){
//    ptau4 = exp(dis[i-1]*tau1) / (1.+exp(tau1));
//    gammart+=(1.-ptau4)*gamma0rt+ptau4*gamma1rt;
//  }
//  gammart=log(gammart / Ni);
//
//  ptau=exp(tau)/(1.+exp(tau));
//  gammart=log((1.-ptau)*gamma0rt+ptau*gamma1rt);

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
      Nk00[i]=nk00[i];
      Nk11[i]=nk11[i];
      Nk01[i]=nk01[i];
      Nk10[i]=nk10[i];
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
      // Add paired on disease
   //   if(i > 0){
   //     ptau4 = exp(tau+(dis[i-1]*dis[i])*tau1) / (1.+exp(tau+(dis[i-1]*dis[i])*tau1));
   //   }else{
   //     ptau4 = exp(tau) / (1.+exp(tau));
   //   }
   //   Next the sequential version
    //  if(dis[i-1]==1){
    //    ptau4 = exp(tau1) / (1.+exp(tau1));
    //  }else{
    //    ptau4 = 1. / (1.+exp(tau1));
    //  }
    //   ptau4 = exp(tau) / (1.+exp(tau));
        if(dis[i-1] == 1){
          ptau4 = exp(tau+tau1) / (1.+exp(tau + tau1));
        }else{
          ptau4 = 1. / (1.+exp(tau1 - tau));
        }
        if(unif_rand() < ptau4){
	  dis[i] = 1;
          /* Now propose unseen size for unit i based on disease status */
          /* In the next two lines a sizei is chosen */
          /* with parameters lnlam1i and nu1i */
          temp = unif_rand();
          for (sizei=1; sizei<=Ki; sizei++){
            if(temp <= p1i[sizei-1]) break;
          }
        }else{
	  dis[i] = 0;
          /* Now propose unseen size for unit i based on non-disease status */
          /* In the next two lines a sizei is chosen */
          /* with parameters lnlam0i and nu0i */
          temp = unif_rand();
          for (sizei=1; sizei<=Ki; sizei++){
            if(temp <= p0i[sizei-1]) break;
          }
        }
       }
      }
      u[i]=sizei; // This sets the unit size for this (unobserved) unit
      if(dis[i]==1){
        Nk1[sizei-1]=Nk1[sizei-1]+1;
        if(dis[i-1]==1){
          Nk11[sizei-1]=Nk11[sizei-1]+1;
        }else{
          Nk01[sizei-1]=Nk01[sizei-1]+1;
	}
      }else{
        Nk0[sizei-1]=Nk0[sizei-1]+1;
        if(dis[i-1]==1){
          Nk10[sizei-1]=Nk10[sizei-1]+1;
        }else{
          Nk00[sizei-1]=Nk00[sizei-1]+1;
	}
      }
  //  if(unif_rand() < ptau){
  //    dis[i]=1;
  //  }else{
  //    dis[i]=0;
  //  }
    }
    discount=discountn;
    dispairs=dispairsn;
    for (i=ni; i<Ni; i++){
      discount+=dis[i];
      dispairs+=(dis[i-1]==dis[i]);
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
      sample[isamp*dimsample+6]=tau;
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
      sample[isamp*dimsample+10]=(double)(discount);
      sample[isamp*dimsample+11]=(double)(dispairs);
      for (i=0; i<Np0; i++){
        sample[isamp*dimsample+12+i]=pdeg0i[i];
      }
      for (i=0; i<Np1; i++){
        sample[isamp*dimsample+12+Np0+i]=pdeg1i[i];
      }
      for (i=0; i<Ki; i++){
        Nk0pos[i]=Nk0pos[i]+Nk0[i];
        Nk1pos[i]=Nk1pos[i]+Nk1[i];
        pos0u[i]+=((Nk0[i]*1.)/Nd);
        pos1u[i]+=((Nk1[i]*1.)/Nd);
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
    pos1u[i]/=dsamp;
  }
  for (i=0; i<ni; i++){
     pop[i]=u[i];
  }
  PutRNGstate();  /* Disable RNG before returning */
  free(p0i);
  free(p1i);
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
  free(tausample);
  free(tau1sample);
}

void MHcmpthetadiseasepaired (int *dis, int *u, int *Nk00, int *Nk10, int *Nk01, int *Nk11,
            int *Nk0, int *Nk1, int *K,
            double *mu0, double *mu1, double *dfmu, 
            double *sigma0, double *sigma1, double *dfsigma,
            double *lnlamproposal, 
            double *nuproposal, 
            double *tauproposal, 
            int *N, int *Np0i, int *Np1i,
	    double *psample0, double *psample1,
            double *lnlamsample0, double *nusample0,
            double *lnlamsample1, double *nusample1,
            double *tausample, double *tau1sample,
            double *logdiseaseprior,
            int *samplesize, int *staken, int *warmuptheta, int *interval,
            int *verbose
         ) {
  int Np0, Np1;
  int step, taken, give_log1=1, give_log0=0;
  int i, Ki, Ni, isamp, iinterval, isamplesize, iwarmuptheta;
  double ip, cutoff;
  double mu0i, mu0star, lnlam0star, lnlam0i, lp;
  double mu1i, mu1star, lnlam1star, lnlam1i;
  double p0is, p0stars;
  double p1is, p1stars;
  double sigma0star, sigma0i, sigma20star, sigma20i, qnu0star, qnu0i;
  double sigma1star, sigma1i, sigma21star, sigma21i, qnu1star, qnu1i;
  double nu0star, nu1star, nu0i, nu1i;
  double ptaui, taui;
  double ptaustar, taustar;
  double ptau1i, tau1i;
  double ptau1star, tau1star;
  double p0ithetastar, p0ithetai, p1ithetastar, p1ithetai;
  double ddfmu, rdfmu, ddfsigma;
  double dmu0, dmu1;
  double dsigma0, dsigma1, dsigma20, dsigma21;
  double dlnlamproposal, dnuproposal;
  double dtauproposal;
  double errval=0.0000000001, lzcmp;

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
  taui = tausample[0];
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
    taustar  = rnorm(taui,  dtauproposal);
    tau1star = rnorm(tau1i, dtauproposal);

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
    ptaustar = ( exp(taustar+tau1star) / (1.+exp(taustar + tau1star)) ); // 1 -> 1
    ptaui= ( exp(taui+tau1i) / (1.+exp(taui + tau1i)) );
    ptau1star = ( 1. / (1.+exp(tau1star - taustar)) ); // 0 -> 1
    ptau1i= ( 1. / (1.+exp(tau1i- taui)) );
    for (i=0; i<Ki; i++){
     if(Nk11[i]>0){
      ip+=Nk11[i]*(log(ptaustar)-log(ptaui));
     }
     if(Nk01[i]>0){
      ip+=Nk01[i]*(log(ptau1star)-log(ptau1i));
     }
     if(Nk10[i]>0){
      ip+=Nk10[i]*(log(1.-ptaustar)-log(1.-ptaui));
     }
     if(Nk00[i]>0){
      ip+=Nk00[i]*(log(1.-ptau1star)-log(1.-ptau1i));
     }
    }
    /* Add the disease status prior */
    ip+=logdiseaseprior[(int)trunc(1000*ptaustar-0.5)];
    ip-=logdiseaseprior[(int)trunc(1000*ptaui-0.5)];
//Rprintf("taustar %f tau1star %f dispairs %d discount %d Ni %d\n", taustar, tau1star, dispairs, discount, Ni);
//Rprintf("d0 %f d1 %f Ips %d Ip %d ips %f ip %f\n", diseaseprior[0], diseaseprior[1],
//	          	(int)trunc(1000*ptaustar+0.5),(int)trunc(1000*ptau+0.5),
//		          log(diseaseprior[(int)trunc(1000*ptaustar+0.5)]),
//		          log(diseaseprior[(int)trunc(1000*ptau+0.5)]) );

//  for (i=0; i<1000; i++){
//Rprintf("i %d logp %f p %f\n",i, log(diseaseprior[i]), (diseaseprior[i]) ) ;
//  }
// Rprintf("ip %f ip %f n1 %f n2 %f\n", (discount*log(ptaustar)+(Ni-discount)*log(1.-ptaustar)),
//                          (discount*log(ptau)+(Ni-discount)*log(1.-ptau)), tmp2-tmp1,tmp2-ip );

    for (i=0; i<Ki; i++){
//   if(Nk00[i]>0){
//    lp = log(p0star[i]*ptaustar/(p0i[i]*ptaui));
//    if(fabs(lp) < 100.){ip += (Nk00[i]*lp);}
//   }
//   if(Nk10[i]>0){
//    lp = log(p0star[i]*(1.-ptau1star)/(p0i[i]*(1.-ptau1i)));
//    if(fabs(lp) < 100.){ip += (Nk01[i]*lp);}
//   }
//   if(Nk11[i]>0){
//    lp = log(p1star[i]*ptau1star/(p1i[i]*ptau1i));
//    if(fabs(lp) < 100.){ip += (Nk11[i]*lp);}
//   }
//   if(Nk01[i]>0){
//    lp = log(p1star[i]*(1.-ptau1star)/(p1i[i]*(1.-ptau1i)));
//    if(fabs(lp) < 100.){ip += (Nk10[i]*lp);}
//   }
//  for (i=0; i<Ki; i++){
//   if(Nk00[i]>0){
//    lp = log(p0star[i]*ptaustar/(p0i[i]*ptaui));
//    if(fabs(lp) < 100.){ip += (Nk00[i]*lp);}
//   }
//   if(Nk10[i]>0){
//    lp = log(p0star[i]*(1.-ptau1star)/(p0i[i]*(1.-ptau1i)));
//    if(fabs(lp) < 100.){ip += (Nk01[i]*lp);}
//   }
//   if(Nk11[i]>0){
//    lp = log(p1star[i]*ptau1star/(p1i[i]*ptau1i));
//    if(fabs(lp) < 100.){ip += (Nk11[i]*lp);}
//   }
//   if(Nk01[i]>0){
//    lp = log(p1star[i]*(1.-ptau1star)/(p1i[i]*(1.-ptau1i)));
//    if(fabs(lp) < 100.){ip += (Nk10[i]*lp);}
//   }

     if(Nk0[i]>0){
      lp = log(p0star[i]/p0i[i]);
      if(fabs(lp) < 100.){ip += (Nk0[i]*lp);}
     }
     if(Nk1[i]>0){
      lp = log(p1star[i]/p1i[i]);
      if(fabs(lp) < 100.){ip += (Nk1[i]*lp);}
     }
//   if(Nk0[i]>0){
//    lp = log(p0star[i]*(1.-ptaustar)/(p0i[i]*(1.-ptaui)));
//    if(fabs(lp) < 100.){ip += (Nk0[i]*lp);}
//   }
//   if(Nk1[i]>0){
//    lp = log(p1star[i]*ptaustar/(p1i[i]*ptaui));
//    if(fabs(lp) < 100.){ip += (Nk1[i]*lp);}
//   }
    }
    /* The logic is to set exp(cutoff) = exp(ip) * qratio ,
    then let the MH probability equal min{exp(cutoff), 1.0}.
    But we'll do it in log space instead.  */
    cutoff = ip + qnu0i-qnu0star + qnu1i-qnu1star;
      
    /* if we accept the proposed network */
    if (cutoff >= 0.0 || log(unif_rand()) < cutoff) { 
      /* Make proposed changes */
      taui = taustar;
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
        tausample[isamp] = taui;
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
