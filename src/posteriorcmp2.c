/*******************************************************************/
/* Computation of the log-likelihood and marginal posterior of size*/
/*******************************************************************/

#include "posteriorcmp.h"
#include "posteriorcmp2.h"
#include "cmp.h"
#include <R.h>
#include <Rmath.h>
#include <math.h>

void gcmp2 (int *pop12,
            int *pop21, 
            int *nk, 
            int *K, 
            int *n1, 
            int *n2, 
            int *n0, 
            int *samplesize, int *burnin, int *interval,
            double *mu, double *kappa, 
            double *sigma,  double *df,
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
  int step, staken, getone=1, intervalone=1, verboseMHcmp = 0;
  int i, ni, Ni, Ki, isamp, iinterval, isamplesize, iburnin;
  int ni1, ni2, ni0;
  double mui, sigmai, dsamp;
  double dkappa, ddf, dmu, dsigma, dmuproposal, dsigmaproposal;
  int tU1, tU2, sizei, imaxN, imaxm, give_log0=0, give_log1=1;
  int maxpop;
  double r1, r2, gammart, pis, Nd;
  double temp;
  double errval=0.0000000001, lzcmp;

  GetRNGstate();  /* R function enabling uniform RNG */

  ni1=(*n1);
  ni2=(*n2);
  ni0=(*n0);
  Ni=(*N);
  Ki=(*K);
  imaxN=(*maxN);
  ni = ni1 + ni2 - ni0;
  imaxm=imaxN-ni;
  isamplesize=(*samplesize);
  iinterval=(*interval);
  iburnin=(*burnin);
  Np=(*Npi);
  dkappa=(*kappa);
  ddf=(*df);
  dsigma=(*sigma);
  dmu=(*mu);
  dsigmaproposal=(*sigmaproposal);
  dmuproposal=(*muproposal);

  dimsample=5+Np;

  double *pi = (double *) malloc(sizeof(double) * Ki);
  double *pd = (double *) malloc(sizeof(double) * Ki);
  int *d1 = (int *) malloc(sizeof(int) * ni1);
  int *d2 = (int *) malloc(sizeof(int) * (ni2+1));
  int *b1 = (int *) malloc(sizeof(int) * ni1);
  int *b2 = (int *) malloc(sizeof(int) * (ni2+1));
  int *Nk = (int *) malloc(sizeof(int) * Ki);
  int *Nkpos = (int *) malloc(sizeof(int) * Ki);
  double *lpm = (double *) malloc(sizeof(double) * imaxm);
  double *pdegi = (double *) malloc(sizeof(double) * (Np+1));
  double *psample = (double *) malloc(sizeof(double) * (Np+1));
  double *musample = (double *) malloc(sizeof(double));
  double *sigmasample = (double *) malloc(sizeof(double));

  maxpop=0;
  for (i=0; i<ni1; i++){
    if((pop12[i]>0) && (pop12[i] <= Ki)){ d1[i]=pop12[i];}
    if(pop12[i]==0){ d1[i]=1;}
    if(pop12[i]>Ki){ d1[i]=Ki;}
    if(pop12[i]>maxpop){maxpop=pop12[i];}
  }
  d2[ni2] = 0;
  for (i=0; i<ni2; i++){
    if((pop21[i]>0) && (pop21[i] <= Ki)){ d2[i]=pop21[i];}
    if(pop21[i]==0){ d2[i]=1;}
    if(pop21[i]>Ki){ d2[i]=Ki;}
    if(pop21[i]>maxpop){maxpop=pop21[i];}
  }
  // b is the cumulative version of d, which is uobs
  // so b1 is cumulative unit sizes for first list
  // b2 is cumulative unit sizes for second list
  b1[ni1-1]=d1[ni1-1];
  for (i=(ni1-2); i>=0; i--){
    b1[i]=b1[i+1]+d1[i];
  }
  b2[ni2]=0;
  if(ni1 > 0){
    b2[ni2-1]=d2[ni2-1];
    for (i=(ni2-2); i>=0; i--){
      b2[i]=b2[i+1]+d2[i];
    }
  }
  for (i=0; i<Ki; i++){
     Nk[i]=nk[i];
     Nkpos[i]=0;
     ppos[i]=0.;
  }
  // tU1 is the total unit sizes from the first list
  tU1=0;
  for (i=ni1; i<Ni; i++){
    tU1+=pop12[i];
  }
  tU2=0;
  for (i=ni2; i<Ni; i++){
    tU2+=pop21[i];
  }
  /* Draw initial phis */
  r1=0.;
  for (i=0; i<ni1; i++){
    r1+=(exp_rand()/(tU1+b1[i]));
  }
  r2=0.;
  for (i=0; i<ni2; i++){
    r2+=(exp_rand()/(tU2+b2[i]));
  }

  for (i=0; i<Np; i++){
     psample[i] = 0.01;
  }
  musample[0] = dmu;
  sigmasample[0] = dsigma;

  isamp = 0;
  step = -iburnin;
  while (isamp < isamplesize) {
    /* Draw new theta */
    /* but less often than the other full conditionals */
    if (step == -iburnin || step==(10*(step/10))) { 
     MHcmptheta(Nk,K,mu,kappa,sigma,df,muproposal,sigmaproposal,
           &Ni, &Np, psample,
	   musample, sigmasample, &getone, &staken, burnintheta, &intervalone, 
	   &verboseMHcmp);
    }

    for (i=0; i<Np; i++){
      pdegi[i] = psample[i];
    }
    mui=musample[0];
    sigmai=sigmasample[0];
//  if(sigmai > 4.0 || mui > 4.5) Rprintf("mui %f sigmai %f kappa %f\n", mui, sigmai, kappa);

    /* Draw new N */

    /* First find the degree distribution */
    pis=0.;
    lzcmp = zcmp(exp(mui), sigmai, errval, Ki, give_log1);
    if(lzcmp < -100000.0){continue;}
    pi[Np]=cmp(Np+1,mui,sigmai,lzcmp,give_log0);
//Rprintf("mui %f sigmai %f lzcmp %f pi %f\n", mui, sigmai, lzcmp, pi[Np]);
    for (i=Np+1; i<Ki; i++){
      pi[i]=pi[i-1]*exp(mui-sigmai*log((double)(i+1)));
    }
//  Rprintf("isamp %d pis %f\n", isamp, pis);
    pis=1.-exp(-lzcmp);
    for (i=0; i<Ki; i++){
      pi[i]/=pis;
//Rprintf("i %d pi %f pi0 %f\n", i, pi[i], pi0[i], pis, pis0);
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
      gammart+=(exp(-(r1 + r2)*(i+1))*pi[i]);
    }
    gammart=log(gammart);
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
		    
    /* Draw phis */
    // tU1 is the total unit sizes from first list
    tU1=0;
    for (i=ni1; i<Ni; i++){
      tU1+=pop12[i];
    }
    tU2=0;
    for (i=ni2; i<Ni; i++){
      tU2+=pop21[i];
    }
    r1=0.;
    for (i=0; i<ni1; i++){
      r1+=(exp_rand()/(tU1+b1[i]));
    }
    r2=0.;
    for (i=0; i<ni2; i++){
      r2+=(exp_rand()/(tU2+b2[i]));
    }

    /* Draw unseen sizes */
    for (i=0; i<Ki; i++){
      Nk[i]=nk[i];
    }
    // Set up pi to be cumulative for random draws
    for (i=1; i<Ki; i++){
//    Rprintf("i %d pi[i] %f\n", i, pi[i]);
      pi[i]=pi[i-1]+pi[i];
    }
    for (i=ni; i<Ni; i++){
      /* Propose unseen size for unit i */
      /* Use rejection sampling */
      sizei=1000000;
      while(sizei >= Ki){
       sizei=1000000;
       while(log(1.0-unif_rand()) > -(r1+r2)*sizei){
        /* Now propose unseen size for unit i */
        /* In the next two lines a sizei is chosen */
        /* with parameters mui and sigmai */
	temp = unif_rand();
//      gammart = pi[Ki-1] * unif_rand();
        for (sizei=1; sizei<=Ki; sizei++){
          if(temp <= pi[sizei-1]) break;
        }
//      Rprintf("sizei %d pi[Ki-1] %f gammart %f\n", sizei, pi[Ki-1],gammart);
       }
      }
//    if(sizei >= Ki){sizei=Ki-1;}
      pop12[i]=sizei;
      pop21[i]=sizei;
//    if((sizei <= 0) | (sizei > Ki-1)) Rprintf("sizei %d r %f\n", sizei,r);
      Nk[sizei-1]=Nk[sizei-1]+1;
    }
    if (step > 0 && step==(iinterval*(step/iinterval))) { 
      /* record statistics for posterity */
      Nd=(double)Ni;
      sample[isamp*dimsample  ]=Nd;
//if(sigmai > 4.0 || mui > 4.5) Rprintf("sample: %f %f\n", mui,sigmai);
// Rprintf("sample: %f %f\n", mui,sigmai);
      sample[isamp*dimsample+1]=mui;
      sample[isamp*dimsample+2]=sigmai;
      sample[isamp*dimsample+3]=(double)(Nk[0]);
      temp=0.0;
      for (i=0; i<Ki; i++){
        temp+=(i+1.0)*Nk[i];
      }
      sample[isamp*dimsample+4]=temp;
      for (i=0; i<Np; i++){
        sample[isamp*dimsample+5+i]=pdegi[i];
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
  for (i=0; i<ni1; i++){
     pop12[i]=d1[i];
  }
  for (i=0; i<ni2; i++){
     pop21[i]=d2[i];
  }
  PutRNGstate();  /* Disable RNG before returning */
  free(pi);
  free(pd);
  free(d1);
  free(d2);
  free(psample);
  free(pdegi);
  free(b1);
  free(b2);
  free(Nk);
  free(Nkpos);
  free(lpm);
  free(musample);
  free(sigmasample);
}
