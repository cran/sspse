/*******************************************************************/
/* Computation of the log-likelihood and marginal posterior of size*/
/*******************************************************************/

#include "posteriorpln.h"
#include <R.h>
#include <Rmath.h>
#include <math.h>

void gpln (int *pop,
            int *nk, 
            int *K, 
            int *n, 
            int *samplesize, int *burnin, int *interval,
            double *mu0, double *kappa0, 
            double *sigma0,  double *df0,
	    int *Npi,
            double *muproposal, 
            double *sigmaproposal, 
            int *N, int *maxN, 
            double *sample, 
            double *ppos, 
            double *lpriorm, 
            int *burnintheta,
	    int *verbose
			 ) {
  int dimsample, Np;
  int step, staken, getone=1, intervalone=1, verboseMHpln = 0;
  int i, ni, Ni, Ki, isamp, iinterval, isamplesize, iburnin;
  double mui, sigmai, dsamp;
  double dkappa0, ddf0, dmu0, dsigma0, dmuproposal, dsigmaproposal;
  int tU, popi, imaxN, imaxm;
  double r, gammart, pis, Nd;

  GetRNGstate();  /* R function enabling uniform RNG */

  ni=(*n);
  Ni=(*N);
  Ki=(*K);
  imaxN=(*maxN);
  imaxm=imaxN-ni;
  isamplesize=(*samplesize);
  iinterval=(*interval);
  iburnin=(*burnin);
  Np=(*Npi);
  dkappa0=(*kappa0);
  ddf0=(*df0);
  dsigma0=(*sigma0);
  dmu0=(*mu0);
  dsigmaproposal=(*sigmaproposal);
  dmuproposal=(*muproposal);

  dimsample=4+Np;

  double *pi = (double *) malloc(sizeof(double) * Ki);
  int *b = (int *) malloc(sizeof(int) * ni);
  int *Nk = (int *) malloc(sizeof(int) * Ki);
  int *Nkpos = (int *) malloc(sizeof(int) * Ki);
  double *lpm = (double *) malloc(sizeof(double) * imaxm);
  double *pdegi = (double *) malloc(sizeof(double) * (Np+1));
  double *psample = (double *) malloc(sizeof(double) * (Np+1));
  double *musample = (double *) malloc(sizeof(double));
  double *sigmasample = (double *) malloc(sizeof(double));

  b[ni-1]=pop[ni-1];
  for (i=(ni-2); i>=0; i--){
    b[i]=b[i+1]+pop[i];
  }
  for (i=0; i<Ki; i++){
     Nk[i]=nk[i];
     Nkpos[i]=0;
     ppos[i]=0.;
  }
  tU=0;
  for (i=ni; i<Ni; i++){
    tU+=pop[i];
  }
  /* Draw phis */
  r=0.;
  for (i=0; i<ni; i++){
    r+=(exp_rand()/(tU+b[i]));
  }

  for (i=0; i<Np; i++){
     psample[i] = 0.01;
  }
  musample[0] = dmu0;
  sigmasample[0] = dsigma0;

  isamp = 0;
  step = -iburnin;
  while (isamp < isamplesize) {
    /* Draw new theta */
    MHpln(Nk,K,mu0,kappa0,sigma0,df0,muproposal,sigmaproposal,
          &Ni, &Np, psample,
	  musample, sigmasample, &getone, &staken, burnintheta, &intervalone, 
	  &verboseMHpln);

    for (i=0; i<Np; i++){
      pdegi[i] = psample[i];
    }
    mui=musample[0];
    sigmai=sigmasample[0];

    /* Draw new N */

    /* First find the degree distribution */
    pis=0.;
    for (i=Np; i<Ki; i++){
      pi[i]=poilog(i+1,mui,sigmai);
//  Rprintf("i %d pi[i] %f\n", i, pi[i]);
//    pis+=pi[i];
    }
//  Rprintf("isamp %d pis %f\n", isamp, pis);
    pis=1.-poilog(0,mui,sigmai);
    for (i=0; i<Ki; i++){
      pi[i]/=pis;
    }
    pis=1.;
    for (i=0; i<Np; i++){
      pis-=pdegi[i];
    }
    for (i=0; i<Ki; i++){
      pi[i]*=pis;
    }
    // !!!!! Why this? For non-parametric piece
    for (i=0; i<Np; i++){
      pi[i]=pdegi[i];
    }
    gammart=0.;
    for (i=0; i<Ki; i++){
      gammart+=(exp(-r*(i+1))*pi[i]);
    }
    gammart=log(gammart);
    tU = -1000000000;
    // N = m + n
    // Compute (log) P(m | \theta and data and \Psi)
    for (i=0; i<imaxm; i++){
      lpm[i]=i*gammart+lgamma(ni+i+1.)-lgamma(i+1.);
//    Add in the (log) prior on m: P(m)
      lpm[i]=lpm[i]+lpriorm[i];
      if(lpm[i] > tU) tU = (int)lpm[i];
    }
    for (i=0; i<imaxm; i++){
      lpm[i]=exp(lpm[i]-tU);
    }
    for (i=1; i<imaxm; i++){
      lpm[i]=lpm[i-1]+lpm[i];
    }
    gammart = lpm[imaxm-1] * unif_rand();
    for (Ni=0; Ni<imaxm; Ni++){
      if(gammart <= lpm[Ni]) break;
    }
    // Add back the sample size
    Ni+= ni;
    if(Ni > imaxN) Ni = imaxN;
		    
    /* Draw phis */
    tU=0;
    for (i=ni; i<Ni; i++){
      tU+=pop[i];
    }
    r=0.;
    for (i=0; i<ni; i++){
//    phi[i]=(tU+b[i])*exp_rand();
      r+=exp_rand()/(tU+b[i]);
    }

    /* Draw unseen sizes */
    for (i=0; i<Ki; i++){
      Nk[i]=nk[i];
    }
    // Set up pi for random draws
    for (i=1; i<Ki; i++){
//    Rprintf("i %d pi[i] %f\n", i, pi[i]);
      pi[i]=pi[i-1]+pi[i];
    }
    for (i=ni; i<Ni; i++){
      /* Use rejection sampling */
      popi=1000000;
      while(popi >= Ki){
       popi=1000000;
       while(log(1.0-unif_rand()) > -r*popi){
        /* Now propose unseen size for unit i */
        /* In the next two lines a popi is chosen */
        /* with parameters mui and sigmai */
        gammart = pi[Ki-1] * unif_rand();
        for (popi=1; popi<=Ni; popi++){
          if(gammart <= pi[popi-1]) break;
        }
//      Rprintf("popi %d pi[Ki-1] %f gammart %f\n", popi, pi[Ki-1],gammart);
       }
      }
//    if(popi >= Ki){popi=Ki-1;}
      pop[i]=popi;
//    if((popi <= 0) | (popi > Ki-1)) Rprintf("popi %d r %f\n", popi,r);
      Nk[popi-1]=Nk[popi-1]+1;
    }
    if (step > 0 && step==(iinterval*(step/iinterval))) { 
      /* record statistics for posterity */
      Nd=(double)Ni;
      sample[isamp*dimsample  ]=Nd;
      sample[isamp*dimsample+1]=mui;
      sample[isamp*dimsample+2]=sigmai;
      sample[isamp*dimsample+3]=(double)(Nk[0]);
      for (i=0; i<Np; i++){
        sample[isamp*dimsample+4+i]=pdegi[i];
      }
      for (i=0; i<Ki; i++){
        Nkpos[i]=Nkpos[i]+Nk[i];
        ppos[i]+=((Nk[i]*1.)/Nd);
      }
      isamp++;
      if (*verbose && isamplesize==(isamp*(isamplesize/isamp))) Rprintf("Taken %d samples...\n", isamp);
//    if (*verbose) Rprintf("Taken %d samples...\n", isamp);
    }
    step++;
  }
  dsamp=((double)isamp);
  for (i=0; i<Ki; i++){
    nk[i]=Nkpos[i];
    ppos[i]/=dsamp;
  }
  PutRNGstate();  /* Disable RNG before returning */
  free(pi);
  free(psample);
  free(pdegi);
  free(b);
  free(Nk);
  free(Nkpos);
  free(lpm);
  free(musample);
  free(sigmasample);
}

void MHpln (int *Nk, int *K,
	    double *mu0, double *kappa0, 
            double *sigma0,  double *df0,
            double *muproposal, 
            double *sigmaproposal, 
            int *N, int *Npi, double *psample,
            double *musample, double *sigmasample,
            int *samplesize, int *staken, int *burnin, int *interval,
	    int *verbose
			 ) {
  int Np;
  int step, taken, give_log1=1;
  int i, Ki, Ni, isamp, iinterval, isamplesize, iburnin;
  double ip, cutoff;
  double mustar, mui, lp;
  double pis, pstars;
  double sigmastar, sigmai, sigma2star, sigma2i, qsigma2star, qsigma2i;
  double pithetastar, pithetai;
  double dkappa0, rkappa0, ddf0, dmu0;
  double dsigma0, dsigma20, dmuproposal, dsigmaproposal;

  GetRNGstate();  /* R function enabling uniform RNG */

  Ki=(*K);
  Np=(*Npi);
  double *pstar = (double *) malloc(sizeof(double) * Ki);
  double *pi = (double *) malloc(sizeof(double) * Ki);
  double *odegstar = (double *) malloc(sizeof(double) * Np);
  double *odegi = (double *) malloc(sizeof(double) * Np);
  double *pdegstar = (double *) malloc(sizeof(double) * Np);
  double *pdegi = (double *) malloc(sizeof(double) * Np);

  Ni=(*N);
  isamplesize=(*samplesize);
  iinterval=(*interval);
  iburnin=(*burnin);
  dkappa0=(*kappa0);
  rkappa0=sqrt(dkappa0);
  ddf0=(*df0);
  dsigma0=(*sigma0);
  dsigma20=(dsigma0*dsigma0);
  dmu0=(*mu0);
  dsigmaproposal=(*sigmaproposal);
  dmuproposal=(*muproposal);
  isamp = taken = 0;
  step = -iburnin;
  pis=1.;
  for (i=0; i<Np; i++){
    pdegi[i] = psample[i];
    pis-=pdegi[i];
  }
  for (i=0; i<Np; i++){
    odegi[i] = log(pdegi[i]/pis);
  }
  mui = musample[0];
  sigmai = sigmasample[0];
  sigma2i  = sigmai*sigmai;
  pithetai = dnorm(mui, dmu0, sigmai/rkappa0, give_log1);
  pithetai = pithetai+dsclinvchisq(sigma2i, ddf0, dsigma20);
  pis=0.;
  for (i=Np; i<Ki; i++){
   pi[i]=poilog(i+1,mui,sigmai);
// pis+=pi[i];
  }
  pis=1.-poilog(0,mui,sigmai);
//    Rprintf("pis %f\n", pis);
  for (i=Np; i<Ki; i++){
   pi[i]/=pis;
  }
  pis=1.;
  for (i=0; i<Np; i++){
    pis-=pdegi[i];
  }
  for (i=Np; i<Ki; i++){
    pi[i]=pi[i]*pis;
  }
  for (i=0; i<Np; i++){
    pi[i]=pdegi[i];
  }
  // Now do the MCMC updates (starting with the burnin updates)
  while (isamp < isamplesize) {
    /* Propose new theta */
    /* Now the degree distribution model parameters */
    for (i=0; i<Np; i++){
      odegstar[i] = rnorm(odegi[i], dmuproposal);
    }
    /* Convert from odds to probabilities */
    pis=1.;
    for (i=0; i<Np; i++){
      pdegstar[i] = exp(odegstar[i]);
      pis+=pdegstar[i];
    }
    for (i=0; i<Np; i++){
      pdegstar[i]/=pis;
    }
    /* Now the degree distribution (log) mean and s.d. parameters */
    mustar = rnorm(mui, dmuproposal);
    sigma2star = sigma2i*exp(rnorm(0., dsigmaproposal));
    sigmastar = sqrt(sigma2star);
    /* Check for magnitude */

//  if(sigma2star > 1000) Rprintf("%f %f %f %f %f\n", mustar, dmu0, sigma2star, dkappa0, sigma2i);
    /* Calculate pieces of the posterior. */
    qsigma2star = dnorm(log(sigma2star/sigma2i)/dsigmaproposal,0.,1.,give_log1)
                  -log(dsigmaproposal*sigma2star);
    pithetastar = dnorm(mustar, dmu0, sigmastar/rkappa0, give_log1);
    pithetastar = pithetastar+dsclinvchisq(sigma2star, ddf0, dsigma20);
    qsigma2i = dnorm(log(sigma2i/sigma2star)/dsigmaproposal,0.,1.,give_log1)
               -log(dsigmaproposal*sigma2i);

    /* Calculate ratio */
    ip = pithetastar-pithetai;
    pstars=0.;
    for (i=Np; i<Ki; i++){
      pstar[i]=poilog(i+1,mustar,sigmastar);
//    pstars+=pstar[i];
    }
    pstars=1.-poilog(0,mustar,sigmastar);
    for (i=Np; i<Ki; i++){
     pstar[i]/=pstars;
    }
    pstars=1.;
    for (i=0; i<Np; i++){
      pstars-=pdegstar[i];
    }
    for (i=Np; i<Ki; i++){
      pstar[i]*=pstars;
    }
    for (i=0; i<Np; i++){
      pstar[i]=pdegstar[i];
    }
    for (i=0; i<Ki; i++){
     if(Nk[i]>0){
      lp = log(pstar[i]/pi[i]);
      if(fabs(lp) < 100.){ip += (Nk[i]*lp);}
     }
    }
    /* The logic is to set exp(cutoff) = exp(ip) * qratio ,
    then let the MH probability equal min{exp(cutoff), 1.0}.
    But we'll do it in log space instead.  */
//  if (*verbose)
//    Rprintf("Now proposing %d MH steps %f ip1...\n", step, ip);
    cutoff = ip + qsigma2i-qsigma2star;
      
//  if (*verbose)
//    Rprintf("Now proposing %d MH steps %f cutoff...\n", step, cutoff);

    /* if we accept the proposed network */
    if (cutoff >= 0.0 || log(unif_rand()) < cutoff) { 
      /* Make proposed changes */
      for (i=0; i<Np; i++){
        odegi[i] = odegstar[i];
        pdegi[i] = pdegstar[i];
      }
      mui    = mustar;
      sigmai = sigmastar;
      sigma2i = sigma2star;
      qsigma2i = qsigma2star;
      pithetai = pithetastar;
      for (i=0; i<Ki; i++){
        pi[i] = pstar[i];
      }
      taken++;
      if (step > 0 && step==(iinterval*(step/iinterval))) { 
        /* record statistics for posterity */
        musample[isamp]=mui;
        sigmasample[isamp]=sigmai;
        for (i=0; i<Np; i++){
          psample[i]=pdegi[i];
        }
        isamp++;
        if (*verbose && isamplesize==(isamp*(isamplesize/isamp))) Rprintf("Taken %d MH samples...\n", isamp);
      }
    }
    step++;
  }
  free(pi);
  free(pstar);
  free(odegi);
  free(odegstar);
  free(pdegi);
  free(pdegstar);
  PutRNGstate();  /* Disable RNG before returning */
  *staken = taken;
}
