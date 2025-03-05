#define MIN(a,b) (((a)<(b))?(a):(b))

typedef struct Block{
  int     B;     // The size of block-columns
  int     r, c;  // the row and column index of the block within the matrix
  double  *a;    // the block coefficients
} block_t;

typedef struct Matrix{
  int     N;      // The matrix size
  int     B;
  int     NB;     // The size in block-columns/rows
  block_t **blocks;
} matrix_t;


typedef enum {POTRF = 0, TRSM, GEMM} Type;

void dgetrf_(int *m, int *n, double *a, int *lda, int *ipiv, int *info);
void dpotrf_(char *uplo, int *n, double *a, int *lda, int *info);

void dpotrs_(char *uplo, int *n, int *nrhs, double *a, int *lda, double *b, int *ldb, int *info);

void dtrsm_(char *side, char *uplo, char *transa, char *diag, 
            int *m, int *n, const double *alpha, const double *A, int *lda, 
            double *B, int *ldb);
void dlarnv_(int *idist, int *iseed, int *n, double *x);
void dgetrs_(char *t, int *n, int *nrhs, double *A, int *lda, int *ipiv, double *x, int *incx, int *info);
void dgemv_(char *t, int *m, int *n, const double *alpha, const double *A, int *lda, const double *x, int *incx, const double *beta, double *y, int *incy);
double dnrm2_c(int n, double *x, int incx);
double dnrmf_c(int m, int n, double *A, int lda);

void dgemm_(char *ta, char *tb, int *m, int *n, int *k, const double *alpha, const double *A, int *lda, const double *B, int *ldB, const double *beta,  const double *c, int *ldc);


void dsymm_(char *side, char *uplo, int *m, int *n, const double *alpha, const double *A, int *lda, const double *B, int *ldB, const double *beta,  const double *c, int *ldc);

void dsyrk_(char *uplo, char *trans, int *n, int *k, const double *alpha, const double *A, int *lda, const double *beta,  const double *c, int *ldc);


long usecs ();
void mysleep(double sec);

void chol_seq              (matrix_t A);
void chol_par_loop_simple  (matrix_t A);
void chol_par_loop_improved(matrix_t A);
void chol_par_tasks        (matrix_t A);


void init_matrix(matrix_t *A, int B, int NB);
void print_matrix(matrix_t A);



void potrf(block_t akk);
void trsm(block_t akk, block_t aik);
void gemm(block_t aik, block_t ajk, block_t aij);

double check_res(matrix_t A, matrix_t Ac);
void copy_matrix(matrix_t A, matrix_t *Ac);
void free_matrix(matrix_t *A);
