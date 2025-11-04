#ifndef POSTERIORCMPDISEASE_H
#define POSTERIORCMPDISEASE_H

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
                         );

void MHcmpthetadiseasepaired (int *dis, int *u, int *Nk0, int *Nk1, int *K,
	    int *idiscountU, int *idispairsn, int *ini,
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
         );
#endif /* POSTERIORCMPDISEASE_H */
