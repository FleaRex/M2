// Copyright 2001 Michael E. Stillman

#include "RR.hpp"
#include <stdio.h>
#include <math.h>
#include "text_io.hpp"
#include "monoid.hpp"
#include "relem.hpp"
#include "ringmap.hpp"
#include "random.hpp"
#include "gbring.hpp"
#include "../d/M2mem.h"
#include "coeffrings.hpp"

#if 0
#define RRELEM_VAL(f) (RRelem ((f).poly_val))
#define RR_VAL(f) ((RRELEM_VAL(f))->val)
#define RR_RINGELEM(a) ((ring_elem) ((Nterm *) (a)))
#endif

#define RRELEM_VAL(f) (reinterpret_cast<RRelem>((f).poly_val))
#define RR_RINGELEM(a) (ring_elem(reinterpret_cast<Nterm *>(a)))
#define RR_VAL(f) ((RRELEM_VAL(f))->val)

RR::~RR()
{
}

bool RR::initialize_RR(double epsilon) 
{
  initialize_ring(0);
  _epsilon = epsilon;

  zeroV = from_int(0);
  oneV = from_int(1);
  minus_oneV = from_int(-1);

  coeffR = new CoefficientRingRR;
  return true;
}

RR *RR::create(double epsilon)
{
  RR *result = new RR;
  result->initialize_RR(epsilon);
  return result;
}


void RR::text_out(buffer &o) const
{
  o << "RR";
}

ring_elem RR::from_int(int n) const
{
  double a = n;
  return RR::from_double(a);
}

RR::RRelem RR::new_elem() const
{
  RRelem result = reinterpret_cast<RRelem>(getmem(sizeof(RRelem_rec)));
  result->val = 0.0;
  return result;
}
ring_elem RR::from_double(double a) const
{
  RRelem result = reinterpret_cast<RRelem>(getmem(sizeof(RRelem_rec)));
  result->val = a;
  return RR_RINGELEM(result);
}
double RR::to_double(ring_elem a)
{
  return RR_VAL(a);
}

ring_elem RR::from_rational(mpq_ptr r) const
{
  RRelem result = reinterpret_cast<RRelem>(getmem(sizeof(RRelem_rec)));
  result->val = mpq_get_d(r);
  return RR_RINGELEM(result);
}
ring_elem RR::from_BigReal(mpf_ptr a) const
{
  RRelem result = reinterpret_cast<RRelem>(getmem(sizeof(RRelem_rec)));
  result->val = mpf_get_d(a);
  return RR_RINGELEM(result);
}

void RR::remove_elem(RRelem f) const
{
}

ring_elem RR::random() const
{
  int d = 1000000;
  long r = Random::random0(2*d);
  double a = (r*1.0)/d - 1.0;
  return RR::from_double(a);
}

int RR::compare_RR(double a, double b) const
  // This is our notion of equality
{
  double c = a-b;
  if (c > _epsilon) return GT;
  if (c < -_epsilon) return LT;
  return EQ;
}

void RR::elem_text_out(buffer &o, const ring_elem ap) const
{
  double a = RR_VAL(ap);

  char s[100];

  bool is_neg = compare_RR(a,0.0) == LT;
  a = fabs(a);
  bool is_one = compare_RR(a,1.0) == EQ;

  if (!is_neg && p_plus) o << '+';
  if (is_neg) o << '-';
  if (is_one) 
    {  
      if (p_one) o << '1'; 
    }
  else
    {
      sprintf(s, "%f", a);
      o << s;
    }
}


ring_elem RR::from_int(mpz_ptr n) const
{
  double a = mpz_get_d(n);
  return RR::from_double(a);
}

bool RR::promote(const Ring *, const ring_elem, ring_elem &) const
{
  return false;
}

bool RR::lift(const Ring *, const ring_elem, ring_elem &) const
{
  return false;
}

bool RR::is_zero_RR(double a) const
{
  return compare_RR(a,0.0) == EQ;
}

bool RR::is_zero(const ring_elem f) const
{
  return compare_RR(RR_VAL(f),0.0) == EQ;;
}

bool RR::is_unit(const ring_elem f) const
{
  return !RR::is_zero(f);
}

bool RR::is_equal(const ring_elem f, const ring_elem g) const
{
  return compare_RR(RR_VAL(f),RR_VAL(g)) == EQ;
}
int RR::compare(const ring_elem f, const ring_elem g) const
{
  return compare_RR(RR_VAL(f),RR_VAL(g));
}
int RR::is_positive(const ring_elem f) const
{
  return compare_RR(RR_VAL(f),0.0) == GT;
}

ring_elem RR::copy(const ring_elem f) const
{
  return RR::from_double(RR_VAL(f));
}

void RR::remove(ring_elem &f) const
{
}

ring_elem RR::preferred_associate(ring_elem f) const
{
  if (RR::is_positive(f) >= 0) return RR::from_double(1.0);
  return RR::from_double(-1.0);
}

void RR::internal_negate_to(ring_elem &f) const
{
  RRelem a = RRELEM_VAL(f);
  a->val = - a->val;
}

void RR::internal_add_to(ring_elem &f, ring_elem &g) const
{
  RRelem a = RRELEM_VAL(f);
  a->val += RR_VAL(g);
  remove(g);
}

void RR::internal_subtract_to(ring_elem &f, ring_elem &g) const
{
  RRelem a = RRELEM_VAL(f);
  a->val -= RR_VAL(g);
  remove(g);
}

ring_elem RR::negate(const ring_elem f) const
{
  return RR::from_double(- RR_VAL(f));
}

ring_elem RR::add(const ring_elem f, const ring_elem g) const
{
  return RR::from_double(RR_VAL(f) + RR_VAL(g));
}

ring_elem RR::subtract(const ring_elem f, const ring_elem g) const
{
  return RR::from_double(RR_VAL(f) - RR_VAL(g));
}

ring_elem RR::mult(const ring_elem f, const ring_elem g) const
{
  return RR::from_double(RR_VAL(f) * RR_VAL(g));
}

ring_elem RR::power(const ring_elem f, int n) const
{
  double a = RR_VAL(f);
  double b = 1.0;
  for (int i=0; i<n; i++)
    b *= a;
  return RR::from_double(b);
}
ring_elem RR::power(const ring_elem f, mpz_t n) const
{
  int n1;
  if (!ZZ::get_si(n1, n)) 
    { ERROR("exponent too large"); }
  return RR::power(f,n1);
}

ring_elem RR::invert(const ring_elem f) const
{
  double result = 1/RR_VAL(f);
  return from_double(result);
}

ring_elem RR::divide(const ring_elem f, const ring_elem g) const
{
  return RR::from_double(RR_VAL(f) / RR_VAL(g));
}

ring_elem RR::remainder(const ring_elem f, const ring_elem g) const
{
  // If g == 0.0 then rem = f
  // If g != 0.0 then rem = 0
  double b = RR_VAL(f);
  if (RR::is_zero(g))
    return RR::from_double(b);
  else
    return RR::from_double(0.0);
}

ring_elem RR::quotient(const ring_elem f, const ring_elem g) const
{
  // If g == 0.0 then rem = f, return 0.
  // If g != 0.0 then rem = 0, return f/g
  double a = RR_VAL(g);
  double b = RR_VAL(f);
  if (RR::is_zero_RR(a))
    return RR::from_double(0.0);
  else
    return RR::from_double(b/a);
}

ring_elem RR::remainderAndQuotient(const ring_elem f, const ring_elem g, 
				  ring_elem &quot) const
{
  // If g == 0.0 then rem = f, quot 0.
  // If g != 0.0 then rem = 0, quot f/g
  double a = RR_VAL(g);
  double b = RR_VAL(f);
  if (RR::is_zero_RR(a))
    {
      quot = RR::from_double(0.0);
      return RR::from_double(b);
    }
  else
    {
      quot = RR::from_double(b/a);
      return RR::from_double(0.0);
    }
}


ring_elem RR::gcd(const ring_elem f, const ring_elem g) const
{
  double a1 = RR_VAL(f);
  double b1 = RR_VAL(g);
  if (RR::is_zero_RR(b1) && RR::is_zero_RR(a1))
    return RR::from_double(0.0);
  else
    return RR::from_double(1.0);
}

ring_elem RR::gcd_extended(const ring_elem f, const ring_elem g, 
			    ring_elem &u, ring_elem &v) const
{
  double a1 = RR_VAL(f);
  double b1 = RR_VAL(g);
  if (!RR::is_zero_RR(b1))
    {
      u = RR::from_double(0.0);
      v = RR::from_double(1/b1);
      return RR::from_double(1.0);
    }
  else if (!RR::is_zero_RR(a1))
    {
      u = RR::from_double(1/a1);
      v = RR::from_double(0.0);
      return RR::from_double(1.0);
    }
  else
    {
      u = RR::from_double(0.0);
      v = RR::from_double(0.0);
      return RR::from_double(0.0);
    }
}

void RR::syzygy(const ring_elem a, const ring_elem b,
	       ring_elem &x, ring_elem &y) const
{
  double a1 = RR_VAL(a);
  double b1 = RR_VAL(b);
  if (RR::is_zero_RR(b1))
    {
      x = RR::from_double(0);
      y = RR::from_double(1);
    }
  else 
    {
      x = RR::from_double(1);
      y = RR::from_double(-a1/b1);
    }
}

ring_elem RR::eval(const RingMap *map, const ring_elem f, int) const
{
  return map->get_ring()->from_double(RR_VAL(f));
}

void RR::degree(const ring_elem, int *d) const
{
  degree_monoid()->one(d);
}
void RR::degree_weights(const ring_elem, const M2_arrayint, int &lo, int &hi) const
{
  lo = hi = 0;
}
int RR::primary_degree(const ring_elem) const
{
  return 0;
}

ring_elem RR::homogenize(const ring_elem f, int, int deg, const M2_arrayint) const
{
  if (deg != 0) 
    ERROR("homogenize: no homogenization exists");
  return f;
}

ring_elem RR::homogenize(const ring_elem f, int, const M2_arrayint) const
{
  return f;
}

// Local Variables:
// compile-command: "make -C $M2BUILDDIR/Macaulay2/e "
// End:
