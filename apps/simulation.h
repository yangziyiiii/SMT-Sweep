#ifndef SIMULATION_H
#define SIMULATION_H


#include <stdbool.h>
#include <stdint.h>
#include <assert.h>
#include <stdlib.h>
#include <gmp.h>
#include "gmpxx.h"
using namespace smt;
using namespace std;

//----------------CONFIG--------------
//------------------------------------
#define BTOR_USE_GMP 1


#define BTOR_BV_TYPE uint32_t
#define BTOR_BV_TYPE_BW (sizeof (BTOR_BV_TYPE) * 8)
static uint32_t hash_primes[] = {333444569u, 76891121u, 456790003u};
#define NPRIMES ((uint32_t) (sizeof hash_primes / sizeof *hash_primes))


struct BtorBitVector
{
  uint32_t width; /* length of bit vector */
#ifdef BTOR_USE_GMP
  mpz_t val;
#else
  uint32_t len;   /* length of 'bits' array */

  /* 'bits' represents the bit vector in 32-bit chunks, first bit of 32-bit bv
   * in bits[0] is MSB, bit vector is 'filled' from LSB, hence spare bits (if
   * any) come in front of the MSB and are zeroed out.
   * E.g., for a bit vector of width 31, representing value 1:
   *
   *    bits[0] = 0 0000....1
   *              ^ ^--- MSB
   *              |--- spare bit
   * */
  BTOR_BV_TYPE bits[];
#endif
};

struct BtorMemMgr
{
  size_t allocated;
  size_t maxallocated;
  size_t sat_allocated;
  size_t sat_maxallocated;
};

typedef struct BtorMemMgr BtorMemMgr;
typedef struct BtorBitVector BtorBitVector;

#define BTOR_NEWN(ptr)                                          \
  do                                                                        \
  {                                                                         \
    (ptr) = (decltype(ptr)) malloc(1 * sizeof *(ptr)); \
  } while (0)

#define BTOR_CNEWN(ptr, nelems)                                        \
  do                                                                       \
  {                                                                        \
    (ptr) = (decltype(ptr)) calloc((nelems), sizeof *(ptr)); \
  } while (0)

#define BTOR_MASK_REM_BITS(bv)                       \
  ((((BTOR_BV_TYPE) 1 << (BTOR_BV_TYPE_BW - 1)) - 1) \
   >> (BTOR_BV_TYPE_BW - 1 - (bv->width % BTOR_BV_TYPE_BW)))

#define BTOR_NEW(ptr) BTOR_NEWN (ptr)

void *
btor_mem_malloc (size_t size)
{
  void *result;
  if (!size) return 0;
  result = malloc (size);
  return result;
}


BtorBitVector *btor_bv_new (uint32_t bw)
{
  assert (bw > 0);

  BtorBitVector *res;
#ifdef BTOR_USE_GMP
  BTOR_NEW (res);
  res->width = bw;
  mpz_init (res->val);
#else
  uint32_t i;
  i = bw / BTOR_BV_TYPE_BW ;
  if(bw % BTOR_BV_TYPE_BW > 0) i += 1;
  assert(i > 0);
  res = static_cast< BtorBitVector *>(malloc (sizeof (BtorBitVector) + i * sizeof (BTOR_BV_TYPE))); //FIXME: change to C++ RAII
  res->len = i;
  res->width = bw;
#endif
  return res;
}

uint32_t btor_bv_hash (const BtorBitVector *bv)
{
  assert (bv);

  uint32_t i, j = 0, n, res = 0;
  uint32_t x, p0, p1;

  res = bv->width * hash_primes[j++];

#ifdef BTOR_USE_GMP
  // least significant limb is at index 0
  mp_limb_t limb;
  for (i = 0, j = 0, n = mpz_size (bv->val); i < n; ++i)
  {
    p0 = hash_primes[j++];
    if (j == NPRIMES) j = 0;
    p1 = hash_primes[j++];
    if (j == NPRIMES) j = 0;
    limb = mpz_getlimbn (bv->val, i);
    if (mp_bits_per_limb == 64)
    {
      uint32_t lo = (uint32_t) limb;
      uint32_t hi = (uint32_t) (limb >> 32);
      x           = lo ^ res;
      x           = ((x >> 16) ^ x) * p0;
      x           = ((x >> 16) ^ x) * p1;
      x           = ((x >> 16) ^ x);
      p0          = hash_primes[j++];
      if (j == NPRIMES) j = 0;
      p1 = hash_primes[j++];
      if (j == NPRIMES) j = 0;
      x = x ^ hi;
    }
    else
    {
      assert (mp_bits_per_limb == 32);
      x = res ^ limb;
    }
    x   = ((x >> 16) ^ x) * p0;
    x   = ((x >> 16) ^ x) * p1;
    res = ((x >> 16) ^ x);
  }
#else
  for (i = 0, j = 0, n = bv->len; i < n; i++)
  {
    p0 = hash_primes[j++];
    if (j == NPRIMES) j = 0;
    p1 = hash_primes[j++];
    if (j == NPRIMES) j = 0;
    x   = bv->bits[i] ^ res;
    x   = ((x >> 16) ^ x) * p0;
    x   = ((x >> 16) ^ x) * p1;
    res = ((x >> 16) ^ x);
  }
#endif
  return res;
}


void btor_bv_set_bit (BtorBitVector *bv, uint32_t pos, uint32_t bit)
{
  assert (bv);
  assert (bit == 0 || bit == 1);
  assert (pos < bv->width);

#ifdef BTOR_USE_GMP
  if (bit)
  {
    mpz_setbit (bv->val, pos);
  }
  else
  {
    mpz_clrbit (bv->val, pos);
  }
#else
  assert (bv->len > 0);
  uint32_t i, j;

  i = pos / BTOR_BV_TYPE_BW;
  j = pos % BTOR_BV_TYPE_BW;
  assert (i < bv->len);

  if (bit)
  {
    bv->bits[bv->len - 1 - i] |= (1u << j);
  }
  else
  {
    bv->bits[bv->len - 1 - i] &= ~(1u << j);
  }
#endif
}


BtorBitVector *btor_bv_const (const char *str, uint32_t bw)
{
  assert ( strlen (str) <= bw);

  BtorBitVector *res;

#ifdef BTOR_USE_GMP
  BTOR_NEW (res);
  res->width = bw;
  mpz_init_set_str (res->val, str, 2);
#else
  uint32_t i, j, bit;
  res = btor_bv_new (bw);
  for (i = 0; i < bw; i++)
  {
    j = bw - 1 - i;
    // assert (str[j] == '0' || str[j] == '1');
    bit = str[j] == '0' ? 0 : 1;
    btor_bv_set_bit (res, i, bit);
  }
#endif
  return res;
}

BtorBitVector *btor_bv_char_to_bv (const char *assignment)
{
  assert (assignment);
  assert (strlen (assignment) > 0);

  BtorBitVector *res;
#ifdef BTOR_USE_GMP
  BTOR_NEW (res);
  res->width = strlen (assignment);
  mpz_init_set_str (res->val, assignment, 2);
#else
  res = btor_bv_const (assignment, strlen (assignment));
#endif
  return res;
}


uint32_t btor_bv_get_bit (const BtorBitVector *bv, uint32_t pos)
{
  assert (bv);
  assert (pos < bv->width);

#ifdef BTOR_USE_GMP
  return mpz_tstbit (bv->val, pos);
#else
  uint32_t i, j;

  i = pos / BTOR_BV_TYPE_BW;
  j = pos % BTOR_BV_TYPE_BW;
  return (bv->bits[bv->len - 1 - i] >> j) & 1;
#endif
}


char *btor_bv_to_char (const BtorBitVector *bv)
{
  assert (bv);

  char *res;
  uint64_t bw = bv->width;

  BTOR_CNEWN (res, bw + 1);
#ifdef BTOR_USE_GMP
  char *tmp     = mpz_get_str (0, 2, bv->val);
  uint64_t n    = strlen (tmp);
  uint64_t diff = bw - n;
  assert (n <= bw);
  memset (res, '0', diff);
  memcpy (res + diff, tmp, n);
  assert (strlen (res) == bw);
  free (tmp);
#else
  uint64_t i;
  uint32_t bit;

  for (i = 0; i < bw; i++)
  {
    bit             = btor_bv_get_bit (bv, i);
    res[bw - 1 - i] = bit ? '1' : '0';
  }
  res[bw] = '\0';
#endif
  return res;
}


uint64_t btor_bv_to_uint64 (const BtorBitVector *bv)
{
  assert (bv);
  assert (bv->width <= sizeof (uint64_t) * 8);

  uint64_t res;

#ifdef BTOR_USE_GMP
  res = mpz_get_ui (bv->val);
#else
  assert (bv->len <= 2);
  uint32_t i;
  res = 0;
  for (i = 0; i < bv->len; i++)
    res |= ((uint64_t) bv->bits[i]) << (BTOR_BV_TYPE_BW * (bv->len - 1 - i));
#endif

  return res;
}

#ifndef BTOR_USE_GMP
#ifndef NDEBUG
static bool
rem_bits_zero_dbg (BtorBitVector *bv)
{
  return (bv->width % BTOR_BV_TYPE_BW == 0
          || (bv->bits[0] >> (bv->width % BTOR_BV_TYPE_BW) == 0));
}
#endif

static void
set_rem_bits_to_zero (BtorBitVector *bv)
{
  if (bv->width != BTOR_BV_TYPE_BW * bv->len)
    bv->bits[0] &= BTOR_MASK_REM_BITS (bv);
}
#endif

BtorBitVector *btor_bv_uint64_to_bv (uint64_t value, uint32_t bw)
{

  assert (bw > 0);

  BtorBitVector *res;

#ifdef BTOR_USE_GMP
  BTOR_NEW(res);
  res->width = bw;
  mpz_init_set_ui (res->val, value);
  mpz_fdiv_r_2exp (res->val, res->val, bw);
#else
  res = btor_bv_new (bw);
  assert (res->len > 0);
  res->bits[res->len - 1] = (BTOR_BV_TYPE) value;
  if (res->width > 32)
    res->bits[res->len - 2] = (BTOR_BV_TYPE) (value >> BTOR_BV_TYPE_BW);

  set_rem_bits_to_zero (res);
  assert (rem_bits_zero_dbg (res));
#endif
  return res;
}


BtorBitVector *btor_bv_add (const BtorBitVector *a, const BtorBitVector *b)
{
  assert (a);
  assert (b);
  assert (a->width == b->width);

  BtorBitVector *res;
  uint32_t bw = a->width;
#ifdef BTOR_USE_GMP
  res = btor_bv_new (bw);
  mpz_add (res->val, a->val, b->val);
  mpz_fdiv_r_2exp (res->val, res->val, bw);
#else
  assert (a->len == b->len);
  int64_t i;
  uint64_t x, y, sum;
  BTOR_BV_TYPE carry;

  if (bw <= 64)
  {
    x   = btor_bv_to_uint64 (a);
    y   = btor_bv_to_uint64 (b);
    res = btor_bv_uint64_to_bv (x + y, bw);
  }
  else
  {
    res   = btor_bv_new (bw);
    carry = 0;
    for (i = a->len - 1; i >= 0; i--)
    {
      sum          = (uint64_t) a->bits[i] + b->bits[i] + carry;
      res->bits[i] = (BTOR_BV_TYPE) sum;
      carry        = (BTOR_BV_TYPE) (sum >> 32);
    }
  }

  set_rem_bits_to_zero (res);
  assert (rem_bits_zero_dbg (res));
#endif
  return res;
}


BtorBitVector *btor_bv_and (const BtorBitVector *a, const BtorBitVector *b)
{
  assert (a);
  assert (b);
  // cout << a->width << " . " << b->width << endl;
  // assert (a->width == b->width);

  BtorBitVector *res;
  uint32_t bw = a->width;
#ifdef BTOR_USE_GMP
  res = btor_bv_new (bw);
  mpz_and (res->val, a->val, b->val);
  mpz_fdiv_r_2exp (res->val, res->val, bw);
#else
  assert (a->len == b->len);
  uint32_t i;

  res = btor_bv_new (bw);
  for (i = 0; i < a->len; i++) res->bits[i] = a->bits[i] & b->bits[i];

  assert (rem_bits_zero_dbg (res));
#endif
  return res;
}

bool btor_bv_is_zero (const BtorBitVector *bv)
{
  assert (bv);

#ifdef BTOR_USE_GMP
  return mpz_cmp_ui (bv->val, 0) == 0;
#else
  uint32_t i;
  for (i = 0; i < bv->len; i++)
    if (bv->bits[i] != 0) return false;
  return true;
#endif
}

bool btor_bv_is_one (const BtorBitVector *bv)
{
  assert (bv);

#ifdef BTOR_USE_GMP
  return mpz_cmp_ui (bv->val, 1) == 0;
#else
  uint32_t i;
  if (bv->bits[bv->len - 1] != 1) return false;
  for (i = 0; i < bv->len - 1; i++)
    if (bv->bits[i] != 0) return false;
  return true;
#endif
}

BtorBitVector *btor_bv_one (uint32_t bw)
{
  assert (bw);

  BtorBitVector *res;
#ifdef BTOR_USE_GMP
  BTOR_NEW (res);
  res->width = bw;
  mpz_init_set_ui (res->val, 1);
#else
  res = btor_bv_new (bw);
  btor_bv_set_bit (res, 0, 1);
#endif
  return res;
}

#define btor_bv_zero(BW) btor_bv_new (BW)

BtorBitVector *btor_bv_implies (const BtorBitVector *a, const BtorBitVector *b)
{
  assert (a);
  assert (b);
  assert (a->width == b->width);
  assert (a->width == 1);

  BtorBitVector *res;
#ifdef BTOR_USE_GMP
  res = btor_bv_is_zero (a) || btor_bv_is_one (b) ? btor_bv_one (1)
                                                  : btor_bv_zero (1);
#else
  assert (a->len == b->len);
  uint32_t i;

  res = btor_bv_new (a->width);
  for (i = 0; i < a->len; i++) res->bits[i] = ~a->bits[i] | b->bits[i];

  set_rem_bits_to_zero (res);
  assert (rem_bits_zero_dbg (res));
#endif
  return res;
}

BtorBitVector *btor_bv_or (const BtorBitVector *a, const BtorBitVector *b)
{
  assert (a);
  assert (b);
  assert (a->width == b->width);

  BtorBitVector *res;
  uint32_t bw = a->width;
#ifdef BTOR_USE_GMP
  res = btor_bv_new (bw);
  mpz_ior (res->val, a->val, b->val);
  mpz_fdiv_r_2exp (res->val, res->val, bw);
#else
  assert (a->len == b->len);
  uint32_t i;

  res = btor_bv_new (bw);
  for (i = 0; i < a->len; i++) res->bits[i] = a->bits[i] | b->bits[i];

  assert (rem_bits_zero_dbg (res));
#endif
  return res;
}

BtorBitVector *btor_bv_nand (const BtorBitVector *a, const BtorBitVector *b)
{
  assert (a);
  assert (b);
  assert (a->width == b->width);

  BtorBitVector *res;
  uint32_t bw = a->width;
#ifdef BTOR_USE_GMP
  res = btor_bv_new (bw);
  mpz_and (res->val, a->val, b->val);
  mpz_com (res->val, res->val);
  mpz_fdiv_r_2exp (res->val, res->val, bw);
#else
  assert (a->len == b->len);
  uint32_t i;

  res = btor_bv_new (bw);
  for (i = 0; i < a->len; i++) res->bits[i] = ~(a->bits[i] & b->bits[i]);

  set_rem_bits_to_zero (res);
  assert (rem_bits_zero_dbg (res));
#endif
  return res;
}

BtorBitVector *btor_bv_nor (const BtorBitVector *a, const BtorBitVector *b)
{
  assert (a);
  assert (b);
  assert (a->width == b->width);

  BtorBitVector *res;
  uint32_t bw = a->width;
#ifdef BTOR_USE_GMP
  res = btor_bv_new (bw);
  mpz_ior (res->val, a->val, b->val);
  mpz_com (res->val, res->val);
  mpz_fdiv_r_2exp (res->val, res->val, bw);
#else
  assert (a->len == b->len);
  uint32_t i;

  res = btor_bv_new (bw);
  for (i = 0; i < a->len; i++) res->bits[i] = ~(a->bits[i] | b->bits[i]);

  set_rem_bits_to_zero (res);
  assert (rem_bits_zero_dbg (res));
#endif
  return res;
}


BtorBitVector *btor_bv_not (const BtorBitVector *bv)
{
  assert (bv);

  BtorBitVector *res;
  uint32_t bw = bv->width;
#ifdef BTOR_USE_GMP
  res = btor_bv_new (bw);
  mpz_com (res->val, bv->val);
  mpz_fdiv_r_2exp (res->val, res->val, bw);
#else
  uint32_t i;
  res = btor_bv_new (bw);
  for (i = 0; i < bv->len; i++) res->bits[i] = ~bv->bits[i];
  set_rem_bits_to_zero (res);
  assert (rem_bits_zero_dbg (res));
#endif
  return res;
}

#if 0
#define BTOR_LOG_MEM(FMT, ARGS...)   \
  do                                 \
  {                                  \
    fputs ("[btorlogmem] ", stdout); \
    printf (FMT, ##ARGS);            \
    fflush (stdout);                 \
  } while (0)
#else
#define BTOR_LOG_MEM(...) \
  do                      \
  {                       \
  } while (0)
#endif

void btor_mem_free (void *p, size_t freed)
{
  assert (!p == !freed);
  BTOR_LOG_MEM ("%p free   %10ld\n", p, freed);
  free (p);
}


void btor_bv_free (BtorBitVector *bv)
{

  assert (bv);
#ifdef BTOR_USE_GMP
  mpz_clear (bv->val);
  btor_mem_free (bv, sizeof (BtorBitVector));
#else
  btor_mem_free (
    bv, sizeof (BtorBitVector) + sizeof (BTOR_BV_TYPE) * bv->len);
#endif
}

int32_t btor_bv_compare (const BtorBitVector *a, const BtorBitVector *b)
{
  assert (a);
  assert (b);

  if (a->width != b->width) return -1;
#ifdef BTOR_USE_GMP
  return mpz_cmp (a->val, b->val);
#else
  uint32_t i;
  /* find index on which a and b differ */
  for (i = 0; i < a->len && a->bits[i] == b->bits[i]; i++)
    ;
  if (i == a->len) return 0;
  if (a->bits[i] > b->bits[i]) return 1;
  assert (a->bits[i] < b->bits[i]);
  return -1;
#endif
}

BtorBitVector *btor_bv_copy (const BtorBitVector *bv)
{
  assert (bv);

  BtorBitVector *res;

  res = btor_bv_new (bv->width);
  assert (res->width == bv->width);
#ifdef BTOR_USE_GMP
  mpz_set (res->val, bv->val);
#else
  assert (res->len == bv->len);
  memcpy (res->bits, bv->bits, sizeof (*(bv->bits)) * bv->len);
#endif
  assert (btor_bv_compare (res, (BtorBitVector *) bv) == 0);
  return res;
}


BtorBitVector *btor_bv_uext (const BtorBitVector *bv, uint32_t len)
{
  assert (bv);

  BtorBitVector *res;
  uint32_t bw;

  if (len == 0)
  {
    return btor_bv_copy (bv);
  }

  bw  = bv->width + len;
  res = btor_bv_new (bw);
#ifdef BTOR_USE_GMP
  mpz_set (res->val, bv->val);
#else
  memcpy (
      res->bits + res->len - bv->len, bv->bits, sizeof (*(bv->bits)) * bv->len);
#endif
  return res;
}

BtorBitVector *btor_bv_slice (const BtorBitVector *bv, uint32_t upper, uint32_t lower) {
  assert (bv);

  BtorBitVector *res;
  uint32_t bw = upper - lower + 1;
#ifdef BTOR_USE_GMP
  res = btor_bv_new (bw);
  mpz_fdiv_r_2exp (res->val, bv->val, upper + 1);
  mpz_fdiv_q_2exp (res->val, res->val, lower);
#else
  uint32_t i, j;

  res = btor_bv_new (bw);
  for (i = lower, j = 0; i <= upper; i++)
    btor_bv_set_bit (res, j++, btor_bv_get_bit (bv, i));

  assert (rem_bits_zero_dbg (res));
#endif
  return res;
}


BtorBitVector *btor_bv_concat (const BtorBitVector *a, const BtorBitVector *b)
{
  assert (a);
  assert (b);

  BtorBitVector *res;
  uint32_t bw = a->width + b->width;
#ifdef BTOR_USE_GMP
  res = btor_bv_new (bw);
  mpz_mul_2exp (res->val, a->val, b->width);
  mpz_add (res->val, res->val, b->val);
  mpz_fdiv_r_2exp (res->val, res->val, bw);
#else
  int64_t i, j, k;
  BTOR_BV_TYPE v;

  res = btor_bv_new (bw);

  j = res->len - 1;

  /* copy bits from bit vector b */
  for (i = b->len - 1; i >= 0; i--) res->bits[j--] = b->bits[i];

  k = b->width % BTOR_BV_TYPE_BW;

  /* copy bits from bit vector a */
  if (k == 0)
  {
    assert (j >= 0);
    for (i = a->len - 1; i >= 0; i--) res->bits[j--] = a->bits[i];
  }
  else
  {
    j += 1;
    assert (res->bits[j] >> k == 0);
    v = res->bits[j];
    for (i = a->len - 1; i >= 0; i--)
    {
      v = v | (a->bits[i] << k);
      assert (j >= 0);
      res->bits[j--] = v;
      v              = a->bits[i] >> (BTOR_BV_TYPE_BW - k);
    }
    assert (j <= 0);
    if (j == 0) res->bits[j] = v;
  }

  assert (rem_bits_zero_dbg (res));
#endif
  return res;
}


BtorBitVector *btor_bv_ite (const BtorBitVector *c,
                            const BtorBitVector *t,
                            const BtorBitVector *e)
{
  assert (c);
  assert (t);
  assert (e);
  assert (t->width == e->width);

  BtorBitVector *res;
#ifdef BTOR_USE_GMP
  res = btor_bv_is_one (c) ? btor_bv_copy (t) : btor_bv_copy (e);
#else
  assert (c->len == 1);
  assert (t->len > 0);
  assert (t->len == e->len);
  BTOR_BV_TYPE cc, nn;
  uint32_t i;

  cc = btor_bv_get_bit (c, 0) ? (~(BTOR_BV_TYPE) 0) : 0;
  nn = ~cc;

  res = btor_bv_new (t->width);
  for (i = 0; i < t->len; i++)
    res->bits[i] = (cc & t->bits[i]) | (nn & e->bits[i]);

  assert (rem_bits_zero_dbg (res));
#endif
  return res;
}


BtorBitVector *btor_bv_eq (const BtorBitVector *a, const BtorBitVector *b)
{
  assert (a);
  assert (b);
  assert (a->width == b->width);

  BtorBitVector *res;
#ifdef BTOR_USE_GMP
  res = mpz_cmp (a->val, b->val) == 0 ? btor_bv_one (1)
                                      : btor_bv_zero (1);
#else
  assert (a->len == b->len);
  uint32_t i, bit;

  res = btor_bv_new (1);
  bit = 1;
  for (i = 0; i < a->len; i++)
  {
    if (a->bits[i] != b->bits[i])
    {
      bit = 0;
      break;
    }
  }
  btor_bv_set_bit (res, 0, bit);

  assert (rem_bits_zero_dbg (res));
#endif
  return res;
}

BtorBitVector *btor_bv_xor (const BtorBitVector *a, const BtorBitVector *b) {
  assert (a);
  assert (b);
  assert (a->width == b->width);

  BtorBitVector *res;
  uint32_t bw = a->width;
#ifdef BTOR_USE_GMP
  res = btor_bv_new (bw);
  mpz_xor (res->val, a->val, b->val);
  mpz_fdiv_r_2exp (res->val, res->val, bw);
#else
  assert (a->len == b->len);
  uint32_t i;

  res = btor_bv_new (bw);
  for (i = 0; i < a->len; i++) res->bits[i] = a->bits[i] ^ b->bits[i];

  assert (rem_bits_zero_dbg (res));
#endif
  return res;
}

BtorBitVector *btor_bv_mul (const BtorBitVector *a, const BtorBitVector *b)
{
  assert (a);
  assert (b);
  assert (a->width == b->width);

  BtorBitVector *res;
  uint32_t bw = a->width;
#ifdef BTOR_USE_GMP
  res = btor_bv_new (bw);
  mpz_mul (res->val, a->val, b->val);
  mpz_fdiv_r_2exp (res->val, res->val, bw);
#else
  assert (a->len == b->len);
  uint32_t i;
  uint64_t x, y;
  BtorBitVector *and, *shift, *add;

  if (bw <= 64)
  {
    x   = btor_bv_to_uint64 (a);
    y   = btor_bv_to_uint64 (b);
    res = btor_bv_uint64_to_bv (x * y, bw);
  }
  else
  {
    res = btor_bv_new (bw);
    for (i = 0; i < bw; i++)
    {
      if (btor_bv_get_bit (b, i))
        and = btor_bv_copy (a);
      else
        and = btor_bv_new (bw);
      shift = btor_bv_sll_uint64 (and, i);
      add   = btor_bv_add (res, shift);
      btor_bv_free (and);
      btor_bv_free (shift);
      btor_bv_free (res);
      res = add;
    }
  }
#endif
  return res;
}

BtorBitVector *btor_bv_int64_to_bv (int64_t value, uint32_t bw) {
  assert (bw > 0);

  BtorBitVector *res;

#ifdef BTOR_USE_GMP
  BTOR_NEW (res);
  res->width = bw;
  mpz_init_set_si (res->val, value);
  mpz_fdiv_r_2exp (res->val, res->val, bw);
#else
  BtorBitVector *tmp;
  res = btor_bv_new (bw);
  assert (res->len > 0);

  /* ensure that all bits > 64 are set to 1 in case of negative values */
  if (value < 0 && bw > 64)
  {
    tmp = btor_bv_not (res);
    btor_bv_free (res);
    res = tmp;
  }

  res->bits[res->len - 1] = (BTOR_BV_TYPE) value;
  if (res->width > 32)
    res->bits[res->len - 2] = (BTOR_BV_TYPE) (value >> BTOR_BV_TYPE_BW);

  set_rem_bits_to_zero (res);
  assert (rem_bits_zero_dbg (res));
#endif
  return res;
}


BtorBitVector *btor_bv_ne (const BtorBitVector *a, const BtorBitVector *b)
{
  assert (a);
  assert (b);
  assert (a->width == b->width);

  BtorBitVector *res;
#ifdef BTOR_USE_GMP
  res = mpz_cmp (a->val, b->val) != 0 ? btor_bv_one (1)
                                      : btor_bv_zero (1);
#else
  assert (a->len == b->len);
  uint32_t i, bit;

  res = btor_bv_new (1);
  bit = 1;
  for (i = 0; i < a->len; i++)
  {
    if (a->bits[i] != b->bits[i])
    {
      bit = 0;
      break;
    }
  }
  btor_bv_set_bit (res, 0, !bit);

  assert (rem_bits_zero_dbg (res));
#endif
  return res;
}

BtorBitVector *
btor_bv_ones (uint32_t bw)
{
  assert (bw);

  BtorBitVector *res;
#ifdef BTOR_USE_GMP
  res = btor_bv_one (bw);
  mpz_mul_2exp (res->val, res->val, bw);
  mpz_sub_ui (res->val, res->val, 1);
#else
  BtorBitVector *tmp;
  tmp = btor_bv_new (bw);
  res = btor_bv_not (tmp);
  btor_bv_free (tmp);
#endif
  return res;
}

BtorBitVector *btor_bv_udiv (const BtorBitVector *a, const BtorBitVector *b)
{
  assert (a);
  assert (b);
  assert (a->width == b->width);

  BtorBitVector *res;
#ifdef BTOR_USE_GMP
  uint32_t bw = a->width;
  if (btor_bv_is_zero (b)) return btor_bv_ones (bw);
  res = btor_bv_new (bw);
  mpz_fdiv_q (res->val, a->val, b->val);
  mpz_fdiv_r_2exp (res->val, res->val, bw);
#else
  assert (a->len == b->len);
  udiv_urem_bv (a, b, &res, 0);
  assert (res);
#endif
  return res;
}


BtorBitVector *btor_bv_neg (const BtorBitVector *bv)
{
  assert (bv);

  BtorBitVector *res;
  uint32_t bw = bv->width;
#ifdef BTOR_USE_GMP
  res = btor_bv_not (bv);
  mpz_add_ui (res->val, res->val, 1);
  mpz_fdiv_r_2exp (res->val, res->val, bw);
#else
  BtorBitVector *not_bv, *one;
  not_bv = btor_bv_not (bv);
  one    = btor_bv_uint64_to_bv (1, bw);
  res    = btor_bv_add (not_bv, one);
  btor_bv_free (not_bv);
  btor_bv_free (one);
#endif
  return res;
}


BtorBitVector *btor_bv_sub (const BtorBitVector *a, const BtorBitVector *b)
{
  assert (a);
  assert (b);
  assert (a->width == b->width);

  BtorBitVector *res;
#ifdef BTOR_USE_GMP
  uint32_t bw = a->width;
  res         = btor_bv_new (bw);
  mpz_sub (res->val, a->val, b->val);
  mpz_fdiv_r_2exp (res->val, res->val, bw);
#else
  assert (a->len == b->len);
  BtorBitVector *negb;

  negb = btor_bv_neg (b);
  res  = btor_bv_add (a, negb);
  btor_bv_free (negb);
#endif
  return res;
}


bool btor_bv_is_true (const BtorBitVector *bv)
{
  assert (bv);

  if (bv->width != 1) return 0;
  return btor_bv_get_bit (bv, 0);
}

bool btor_bv_is_false (const BtorBitVector *bv)
{
  assert (bv);

  if (bv->width != 1) return 0;
  return !btor_bv_get_bit (bv, 0);
}


BtorBitVector *btor_bv_sext (const BtorBitVector *bv, uint32_t len)
{
  assert (bv);

  BtorBitVector *res;
  uint32_t bw;

  if (len == 0)
  {
    return btor_bv_copy (bv);
  }

  bw = bv->width;
#ifdef BTOR_USE_GMP
  if (btor_bv_get_bit (bv, bw - 1))
  {
    size_t i, n;
    res = btor_bv_copy (bv);
    res->width += len;
    for (i = bw, n = bw + len; i < n; i++) mpz_setbit (res->val, i);
  }
  else
  {
    res = btor_bv_uext (bv, len);
  }
#else
  BtorBitVector *tmp;
  tmp = btor_bv_get_bit (bv, bw - 1) ? btor_bv_ones (len)
                                     : btor_bv_zero (len);
  res = btor_bv_concat (tmp, bv);
  btor_bv_free (tmp);
  assert (rem_bits_zero_dbg (res));
#endif
  return res;
}

BtorBitVector *btor_bv_ult (const BtorBitVector *a, const BtorBitVector *b)
{
  assert (a);
  assert (b);
  assert (a->width == b->width);

  BtorBitVector *res;
#ifdef BTOR_USE_GMP
  res =
      mpz_cmp (a->val, b->val) < 0 ? btor_bv_one (1) : btor_bv_zero (1);
#else
  assert (a->len == b->len);
  uint32_t i, bit;

  res = btor_bv_new (1);
  bit = 1;

  /* find index on which a and b differ */
  for (i = 0; i < a->len && a->bits[i] == b->bits[i]; i++)
    ;

  /* a >= b */
  if (i == a->len || a->bits[i] >= b->bits[i]) bit = 0;

  btor_bv_set_bit (res, 0, bit);

  assert (rem_bits_zero_dbg (res));
#endif
  return res;
}

BtorBitVector *btor_bv_ulte (const BtorBitVector *a, const BtorBitVector *b)
{
  assert (a);
  assert (b);
  assert (a->width == b->width);

  BtorBitVector *res;
#ifdef BTOR_USE_GMP
  res = mpz_cmp (a->val, b->val) <= 0 ? btor_bv_one (1)
                                      : btor_bv_zero (1);
#else
  assert (a->len == b->len);
  uint32_t i, bit;

  res = btor_bv_new (1);
  bit = 1;

  /* find index on which a and b differ */
  for (i = 0; i < a->len && a->bits[i] == b->bits[i]; i++)
    ;

  /* a > b */
  if (i < a->len && a->bits[i] > b->bits[i]) bit = 0;

  btor_bv_set_bit (res, 0, bit);

  assert (rem_bits_zero_dbg (res));
#endif
  return res;
}

BtorBitVector *btor_bv_ugt (const BtorBitVector *a, const BtorBitVector *b)
{
  assert (a);
  assert (b);
  assert (a->width == b->width);

  BtorBitVector *res;
#ifdef BTOR_USE_GMP
  res =
      mpz_cmp (a->val, b->val) > 0 ? btor_bv_one (1) : btor_bv_zero (1);
#else
  assert (a->len == b->len);
  uint32_t i, bit;

  res = btor_bv_new (1);
  bit = 1;

  /* find index on which a and b differ */
  for (i = 0; i < a->len && a->bits[i] == b->bits[i]; i++)
    ;

  /* a <= b */
  if (i == a->len || a->bits[i] <= b->bits[i]) bit = 0;

  btor_bv_set_bit (res, 0, bit);

  assert (rem_bits_zero_dbg (res));
#endif
  return res;
}

BtorBitVector *btor_bv_ugte (const BtorBitVector *a, const BtorBitVector *b)
{
  assert (a);
  assert (b);
  assert (a->width == b->width);

  BtorBitVector *res;
#ifdef BTOR_USE_GMP
  res = mpz_cmp (a->val, b->val) >= 0 ? btor_bv_one (1)
                                      : btor_bv_zero (1);
#else
  assert (a->len == b->len);
  uint32_t i, bit;

  res = btor_bv_new (1);
  bit = 1;

  /* find index on which a and b differ */
  for (i = 0; i < a->len && a->bits[i] == b->bits[i]; i++)
    ;

  /* a < b */
  if (i < a->len && a->bits[i] < b->bits[i]) bit = 0;

  btor_bv_set_bit (res, 0, bit);

  assert (rem_bits_zero_dbg (res));
#endif
  return res;
}


BtorBitVector *btor_bv_slt (const BtorBitVector *a, const BtorBitVector *b)
{
  assert (a);
  assert (b);
  assert (a->width == b->width);

  BtorBitVector *res;
  uint32_t bw, msb_a, msb_b;

  bw    = a->width;
  msb_a = btor_bv_get_bit (a, bw - 1);
  msb_b = btor_bv_get_bit (b, bw - 1);
  if (msb_a && !msb_b)
  {
    res = btor_bv_one (1);
  }
  else if (!msb_a && msb_b)
  {
    res = btor_bv_zero (1);
  }
  else
  {
    res = btor_bv_ult (a, b);
  }
  return res;
}

BtorBitVector *
btor_bv_slte (const BtorBitVector *a, const BtorBitVector *b)
{
  assert (a);
  assert (b);
  assert (a->width == b->width);

  BtorBitVector *res;
  uint32_t bw, msb_a, msb_b;

  bw    = a->width;
  msb_a = btor_bv_get_bit (a, bw - 1);
  msb_b = btor_bv_get_bit (b, bw - 1);
  if (msb_a && !msb_b)
  {
    res = btor_bv_one (1);
  }
  else if (!msb_a && msb_b)
  {
    res = btor_bv_zero (1);
  }
  else
  {
    res = btor_bv_ulte (a, b);
  }
  return res;
}

BtorBitVector *btor_bv_sgt (const BtorBitVector *a, const BtorBitVector *b)
{
  assert (a);
  assert (b);
  assert (a->width == b->width);

  BtorBitVector *res;
  uint32_t bw, msb_a, msb_b;

  bw    = a->width;
  msb_a = btor_bv_get_bit (a, bw - 1);
  msb_b = btor_bv_get_bit (b, bw - 1);
  if (msb_a && !msb_b)
  {
    res = btor_bv_zero (1);
  }
  else if (!msb_a && msb_b)
  {
    res = btor_bv_one (1);
  }
  else
  {
    res = btor_bv_ugt (a, b);
  }
  return res;
}

BtorBitVector *btor_bv_sgte (const BtorBitVector *a, const BtorBitVector *b)
{
  assert (a);
  assert (b);
  assert (a->width == b->width);

  BtorBitVector *res;
  uint32_t bw, msb_a, msb_b;

  bw    = a->width;
  msb_a = btor_bv_get_bit (a, bw - 1);
  msb_b = btor_bv_get_bit (b, bw - 1);
  if (msb_a && !msb_b)
  {
    res = btor_bv_zero (1);
  }
  else if (!msb_a && msb_b)
  {
    res = btor_bv_one (1);
  }
  else
  {
    res = btor_bv_ugte (a, b);
  }
  return res;
}

BtorBitVector *btor_bv_xnor (const BtorBitVector *a, const BtorBitVector *b)
{
  assert (a);
  assert (b);
  assert (a->width == b->width);

  BtorBitVector *res;
  uint32_t bw = a->width;
#ifdef BTOR_USE_GMP
  res = btor_bv_new (bw);
  mpz_xor (res->val, a->val, b->val);
  mpz_com (res->val, res->val);
  mpz_fdiv_r_2exp (res->val, res->val, bw);
#else
  assert (a->len == b->len);
  uint32_t i;

  res = btor_bv_new (bw);
  for (i = 0; i < a->len; i++) res->bits[i] = a->bits[i] ^ ~b->bits[i];

  set_rem_bits_to_zero (res);
  assert (rem_bits_zero_dbg (res));
#endif
  return res;
}


BtorBitVector *btor_bv_urem (const BtorBitVector *a, const BtorBitVector *b)
{
  assert (a);
  assert (b);
  assert (a->width == b->width);

  BtorBitVector *res;
#ifdef BTOR_USE_GMP
  uint32_t bw = a->width;
  if (btor_bv_is_zero (b)) return btor_bv_copy (a);
  res = btor_bv_new (bw);
  mpz_fdiv_r (res->val, a->val, b->val);
  mpz_fdiv_r_2exp (res->val, res->val, bw);
#else
  assert (a->len == b->len);
  udiv_urem_bv (a, b, 0, &res);
  assert (res);
#endif
  return res;
}

BtorBitVector *btor_bv_sdiv (const BtorBitVector *a, const BtorBitVector *b)
{
  assert (a);
  assert (b);
  assert (a->width == b->width);

  bool is_signed_a, is_signed_b;
  uint32_t bw;
  BtorBitVector *res, *div, *neg_a, *neg_b;

  bw          = a->width;
  is_signed_a = btor_bv_get_bit (a, bw - 1);
  is_signed_b = btor_bv_get_bit (b, bw - 1);

  if (is_signed_a && !is_signed_b)
  {
    neg_a = btor_bv_neg (a);
    div   = btor_bv_udiv (neg_a, b);
    res   = btor_bv_neg (div);
    btor_bv_free (neg_a);
    btor_bv_free (div);
  }
  else if (!is_signed_a && is_signed_b)
  {
    neg_b = btor_bv_neg (b);
    div   = btor_bv_udiv (a, neg_b);
    res   = btor_bv_neg (div);
    btor_bv_free (neg_b);
    btor_bv_free (div);
  }
  else if (is_signed_a && is_signed_b)
  {
    neg_a = btor_bv_neg (a);
    neg_b = btor_bv_neg (b);
    res   = btor_bv_udiv (neg_a, neg_b);
    btor_bv_free (neg_a);
    btor_bv_free (neg_b);
  }
  else
  {
    res = btor_bv_udiv (a, b);
  }
  return res;
}

BtorBitVector *btor_bv_srem (const BtorBitVector *a, const BtorBitVector *b)
{
  assert (a);
  assert (b);
  assert (a->width == b->width);

  bool is_signed_a, is_signed_b;
  uint32_t bw;
  BtorBitVector *res, *rem, *neg_a, *neg_b;

  bw          = a->width;
  is_signed_a = btor_bv_get_bit (a, bw - 1);
  is_signed_b = btor_bv_get_bit (b, bw - 1);

  if (is_signed_a && !is_signed_b)
  {
    neg_a = btor_bv_neg (a);
    rem   = btor_bv_urem (neg_a, b);
    res   = btor_bv_neg (rem);
    btor_bv_free (neg_a);
    btor_bv_free (rem);
  }
  else if (!is_signed_a && is_signed_b)
  {
    neg_b = btor_bv_neg (b);
    res   = btor_bv_urem (a, neg_b);
    btor_bv_free (neg_b);
  }
  else if (is_signed_a && is_signed_b)
  {
    neg_a = btor_bv_neg (a);
    neg_b = btor_bv_neg (b);
    rem   = btor_bv_urem (neg_a, neg_b);
    res   = btor_bv_neg (rem);
    btor_bv_free (neg_a);
    btor_bv_free (neg_b);
    btor_bv_free (rem);
  }
  else
  {
    res = btor_bv_urem (a, b);
  }
  return res;
}

BtorBitVector *btor_bv_srl_uint64 (const BtorBitVector *a, uint64_t shift)
{
  assert (a);

  BtorBitVector *res;

  res = btor_bv_new (a->width);
  if (shift >= a->width) return res;
#ifdef BTOR_USE_GMP
  mpz_fdiv_q_2exp (res->val, a->val, shift);
#else
  uint32_t skip, i, j, k;
  BTOR_BV_TYPE v;
  k = shift % BTOR_BV_TYPE_BW;
  skip = shift / BTOR_BV_TYPE_BW;
  v = 0;
  for (i = 0, j = skip; i < a->len && j < a->len; i++, j++)
  {
    v = (k == 0) ? a->bits[i] : v | (a->bits[i] >> k);
    res->bits[j] = v;
    v = (k == 0) ? a->bits[i] : a->bits[i] << (BTOR_BV_TYPE_BW - k);
  }
  assert (rem_bits_zero_dbg (res));
#endif
  return res;
}


#ifdef BTOR_USE_GMP
static uint32_t
get_limb (const BtorBitVector *bv,
          mp_limb_t *limb,
          uint32_t nbits_rem,
          bool zeros)
{
  /* GMP normalizes the limbs, the left most (most significant) is never 0 */
  uint32_t i, n_limbs, n_limbs_total;
  mp_limb_t res = 0u, mask;

  n_limbs = mpz_size (bv->val);

  /* for leading zeros */
  if (zeros)
  {
    *limb = n_limbs ? mpz_getlimbn (bv->val, n_limbs - 1) : 0;
    return n_limbs;
  }

  /* for leading ones */
  n_limbs_total = bv->width / mp_bits_per_limb + (nbits_rem ? 1 : 0);
  if (n_limbs != n_limbs_total)
  {
    /* no leading ones, simulate */
    *limb = nbits_rem ? ~(~((mp_limb_t) 0) << nbits_rem) : ~((mp_limb_t) 0);
    return n_limbs_total;
  }
  mask = ~((mp_limb_t) 0) << nbits_rem;
  for (i = 0; i < n_limbs; i++)
  {
    res = mpz_getlimbn (bv->val, n_limbs - 1 - i);
    if (nbits_rem && i == 0)
    {
      res = res | mask;
    }
    res = ~res;
    if (res > 0) break;
  }
  *limb = res;
  return n_limbs - i;
}
#else
static uint32_t
get_limb (const BtorBitVector *bv,
          BTOR_BV_TYPE *limb,
          uint32_t nbits_rem,
          bool zeros)
{
  uint32_t i;
  BTOR_BV_TYPE res = 0u, mask;

  /* for leading zeros */
  if (zeros)
  {
    for (i = 0; i < bv->len; i++)
    {
      res = bv->bits[i];
      if (res > 0) break;
    }
  }
  /* for leading ones */
  else
  {
    mask = ~((BTOR_BV_TYPE) 0) << nbits_rem;
    for (i = 0; i < bv->len; i++)
    {
      res = bv->bits[i];
      if (nbits_rem && i == 0)
      {
        res = res | mask;
      }
      res = ~res;
      if (res > 0) break;
    }
  }

  *limb = res;
  return bv->len - i;
}
#endif



static uint32_t
get_num_leading (const BtorBitVector *bv, bool zeros)
{
  assert (bv);

  uint32_t res = 0, nbits_pad;
  /* The number of limbs required to represent the actual value.
   * Zero limbs are disregarded. */
  uint32_t n_limbs;
  /* Number of limbs required when representing all bits. */
  uint32_t n_limbs_total;
  /* The number of bits that spill over into the most significant limb,
   * assuming that all bits are represented). Zero if the bit-width is a
   * multiple of n_bits_per_limb. */
  uint32_t nbits_rem;
  uint32_t nbits_per_limb;
#ifdef BTOR_USE_GMP
  mp_limb_t limb;
#else
  BTOR_BV_TYPE limb;
#endif

#ifdef BTOR_USE_GMP
  nbits_per_limb = mp_bits_per_limb;
#else
  nbits_per_limb = BTOR_BV_TYPE_BW;
#endif

  nbits_rem = bv->width % nbits_per_limb;

  n_limbs = get_limb (bv, &limb, nbits_rem, zeros);
  if (n_limbs == 0) return bv->width;

#if defined(__GNUC__) || defined(__clang__)
  res = nbits_per_limb == 64 ? __builtin_clzll (limb) : __builtin_clz (limb);
#else
  res = clz_limb (nbits_per_limb, limb);
#endif
  n_limbs_total = bv->width / nbits_per_limb + 1;
  nbits_pad     = nbits_per_limb - nbits_rem;
  res += (n_limbs_total - n_limbs) * nbits_per_limb - nbits_pad;
  return res;
}

uint32_t btor_bv_get_num_leading_zeros (const BtorBitVector *bv)
{
  return get_num_leading (bv, true);
}

static bool shift_is_uint64 (
                 const BtorBitVector *b,
                 uint64_t *res)
{
  assert (b);
  assert (res);

  uint64_t zeroes;
  BtorBitVector *shift;

  if (b->width <= 64)
  {
    *res = btor_bv_to_uint64 (b);
    return true;
  }

  zeroes = btor_bv_get_num_leading_zeros (b);
  if (zeroes < b->width - 64) return false;

  shift =
      btor_bv_slice (b, zeroes < b->width ? b->width - 1 - zeroes : 0, 0);
  assert (shift->width <= 64);
  *res = btor_bv_to_uint64 (shift);
  btor_bv_free (shift);
  return true;
}

BtorBitVector *btor_bv_srl (const BtorBitVector *a, const BtorBitVector *b)
{
  assert (a);
  assert (b);
  assert (a->width == b->width);

  uint64_t ushift;

  if (shift_is_uint64 (b, &ushift))
  {
    return btor_bv_srl_uint64 (a, ushift);
  }
  return btor_bv_new (a->width);
}

BtorBitVector *btor_bv_sra (const BtorBitVector *a, const BtorBitVector *b)
{
  assert (a);
  assert (b);
  assert (a->width == b->width);

  BtorBitVector *res;
  if (btor_bv_get_bit (a, a->width - 1))
  {
    BtorBitVector *not_a       = btor_bv_not (a);
    BtorBitVector *not_a_srl_b = btor_bv_srl (not_a, b);
    res                        = btor_bv_not (not_a_srl_b);
    btor_bv_free (not_a);
    btor_bv_free (not_a_srl_b);
  }
  else
  {
    res = btor_bv_srl (a, b);
  }
#ifndef BTOR_USE_GMP
  assert (rem_bits_zero_dbg (res));
#endif
  return res;
}


#ifndef NDEBUG
static bool
check_bits_sll_dbg (const BtorBitVector *bv,
                    const BtorBitVector *res,
                    uint32_t shift)
{
  assert (bv);
  assert (res);
  assert (bv->width == res->width);

  uint32_t i;

  if (shift >= bv->width)
  {
    for (i = 0; i < bv->width; i++) assert (btor_bv_get_bit (bv, i) == 0);
  }
  else
  {
    for (i = 0; shift + i < bv->width; i++)
      assert (btor_bv_get_bit (bv, i) == btor_bv_get_bit (res, shift + i));
  }

  return true;
}
#endif


BtorBitVector *btor_bv_sll_uint64 (const BtorBitVector *a, uint64_t shift)
{
  assert (a);

  BtorBitVector *res;
  uint32_t bw = a->width;

  res = btor_bv_new (bw);
  if (shift >= bw) return res;

#ifdef BTOR_USE_GMP
  mpz_mul_2exp (res->val, a->val, shift);
  mpz_fdiv_r_2exp (res->val, res->val, bw);
#else
  uint32_t skip, i, j, k;
  BTOR_BV_TYPE v;

  k    = shift % BTOR_BV_TYPE_BW;
  skip = shift / BTOR_BV_TYPE_BW;

  v = 0;
  for (i = a->len - 1, j = res->len - 1 - skip;; i--, j--)
  {
    v            = (k == 0) ? a->bits[i] : v | (a->bits[i] << k);
    res->bits[j] = v;
    v            = (k == 0) ? a->bits[i] : a->bits[i] >> (BTOR_BV_TYPE_BW - k);
    if (i == 0 || j == 0) break;
  }
  set_rem_bits_to_zero (res);
  assert (rem_bits_zero_dbg (res));
#endif
  assert (check_bits_sll_dbg (a, res, shift));
  return res;
}


BtorBitVector *btor_bv_sll (const BtorBitVector *a, const BtorBitVector *b)
{
  assert (a);
  assert (b);
  assert (a->width == b->width);

  uint64_t ushift;

  if (shift_is_uint64 (b, &ushift))
  {
    return btor_bv_sll_uint64 (a, ushift);
  }
  return btor_bv_new (a->width);
}

#endif