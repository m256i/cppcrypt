#include <cassert>
#include <cmath>
#include <flint/fmpz.h>
#include <flint/fmpz_mod_poly.h>
#include <flint/fmpz_mod_poly_factor.h>
#include <flint/fmpz_mod.h>
#include <ios>
#include <iostream>
#include <chrono>
#include <utility>
#include <vector>
#include <bitset>
#include <string>
#include "crypto.h"
#include <unistd.h>

#include <flint/flint.h>

using namespace blue_crypto;
using ix = GmpWrapper;

struct perf_
{
  perf_(std::string  _name) : name(std::move(_name)) { start = std::chrono::high_resolution_clock::now(); }

  ~perf_()
  {
    auto stop     = std::chrono::high_resolution_clock::now();
    auto duration = std::chrono::duration_cast<std::chrono::microseconds>(stop - start);
    std::cout << name << ": " << duration.count() << " microseconds" << std::endl;
  }

  std::string name;
  decltype(std::chrono::high_resolution_clock::now()) start;
};

ix
ix_abs(const ix& _n)
{
  return _n < 0 ? _n * -1 : _n;
}

[[gnu::pure]] std::pair<ix, ix>
divmod(const ix& _na, const ix& _nb) noexcept
{
  return {_na / _nb, _na % _nb};
}

[[gnu::pure]] std::pair<ix, ix>
extended_gcd(const ix& aa, const ix& bb) noexcept
{
  ix lastremainder = ix_abs(aa);
  ix remainder     = ix_abs(bb);

  ix x, lasty = 0;
  ix y, lastx = 1;

  ix quotient;

  while (remainder != 0)
  {
    ix oldremainder = remainder;

    const auto dm = divmod(lastremainder, remainder);

    quotient  = dm.first;
    remainder = dm.second;

    lastremainder = oldremainder;

    const ix tmp_x = x;
    x              = lastx - quotient * x;
    lastx          = tmp_x;

    const ix tmp_y = y;
    y              = lasty - quotient * y;
    lasty          = tmp_y;
  }

  return {lastremainder, lastx * (aa < 0 ? -1 : 1)};
}

[[gnu::pure]] ix
modinv(const ix& a, const ix& m) noexcept
{
  assert(a != 0);
  const auto gx = extended_gcd(a, m);
  return gx.second % m;
}

struct crv_p
{
  ix x{}, y{};

  void
  print() const
  {
    std::cout << "[";
    x.write();
    std::cout << ", ";
    y.write();
    std::cout << "]\n";
  }

  bool
  operator==(const crv_p& other) const
  {
    return (x == other.x) && (y == other.y);
  }

  bool
  operator!=(const crv_p& other) const
  {
    return !(this->operator==(other));
  }

};

struct jcbn_crv_p
{
  ix x{}, y{}, z{};

  void
  print() const
  {
    std::cout << "[";
    x.write();
    std::cout << ", ";
    y.write();
    std::cout << ", ";
    z.write();
    std::cout << "]\n";
  }

  bool
  operator==(const jcbn_crv_p& other) const
  {
    return (x == other.x) && (y == other.y) && (z == other.z);
  }

  bool
  operator!=(const jcbn_crv_p& other) const
  {
    return !(this->operator==(other));
  }
};

static const crv_p a_identity_element      = {0, 0};
static const jcbn_crv_p j_identity_element = {1, 1, 0};

jcbn_crv_p
to_jacobian(const crv_p& _ws_point)
{
  return {_ws_point.x, _ws_point.y, ix{1}};
}

crv_p
from_jacobian(const jcbn_crv_p& _jcbn, const ix& _p)
{
  if (_jcbn == j_identity_element ||_jcbn.z == 0)
  {
    return a_identity_element;
  }

  ix inv = modinv(_jcbn.z, _p);
  return  {_jcbn.x * inv.pow(2) % _p, _jcbn.y * inv.pow(3) % _p};
}

/* NOTE when using curves where a != 0 this needs to be changed */

jcbn_crv_p
point_double(const jcbn_crv_p& _p1, const ix& _p)
{
  if (_p1.y == 0) [[unlikely]] {
    return j_identity_element;
  }

  const ix a = (_p1.x * 4) * _p1.y.pow(2);
  const ix b = _p1.x.pow(2) * 3/* + a * _p1.z.pow(4) */;

  jcbn_crv_p out;

  out.x = (b.pow(2) - 2 * a) % _p;
  out.y = ((_p1.y.pow(4) * -8) + b * (a - out.x)) % _p;
  out.z = (_p1.y * _p1.z * 2) % _p;

  return out;
}

/* TODO: fix */
jcbn_crv_p
point_add(const jcbn_crv_p& _p1, const jcbn_crv_p& _p2, const ix& _p)
{
  if (_p1 == j_identity_element) 
  {
    return {_p2.x, _p2.y, _p2.z};
  }
  else if (_p2 == j_identity_element)
  {
    return {_p1.x, _p1.y, _p1.z};
  }

  const ix U1 = _p1.x * _p2.z.pow(2);
  const ix U2 = _p2.x * _p1.z.pow(2);
  const ix S1 = _p1.y * _p2.z.pow(3);
  const ix S2 = _p2.y * _p1.z.pow(3);

  if (U1 == U2) [[unlikely]]
  {
    if (S1 != S2) [[unlikely]] {
      return j_identity_element;
    }
    else {
      return point_double(_p1, _p);
    }
  }

  jcbn_crv_p out;

  const ix H = U2 - U1;
  const ix R = S2 - S1;

  out.x = (R.pow(2) - H.pow(3) - 2 * U1 * H.pow(2)) % _p;
  out.y = (R * (U1 * H.pow(2) - out.x) - S1 * H.pow(3)) % _p;
  out.z = (H * _p1.z * _p2.z) % _p;
  
  if (out.z == 0) [[unlikely]]
  {
    out = j_identity_element;
  }

  return out;
}


[[gnu::pure]] inline std::size_t
bits_to_represent(const ix& _num) noexcept
{
  return _num.bitlength(); 
}

[[gnu::pure]] inline bool
is_bit_set(const ix& _num, std::size_t _bid) noexcept
{
  return bool(_num.get_bit(_bid));
}

/* possibly look at:

https://doi.org/10.1016/j.jksuci.2019.07.013
https://link.springer.com/chapter/10.1007/978-3-540-73074-3_15

SIKE all of these papers had errors and typos, i wrote this shit myself :/
*/

static constexpr std::size_t window_size = 4;

std::vector<jcbn_crv_p>
precompute(const jcbn_crv_p& Q, const ix& _p)
{
  const auto count = (std::size_t)std::pow(2, window_size);
  
  std::vector<jcbn_crv_p> out;
  out.reserve(count);
  
  out.push_back(j_identity_element);
  out.push_back(Q);

  jcbn_crv_p next{Q}; // 1P

  for (std::size_t i = 2; i != count; ++i)
  {
    next = point_add(Q, next, _p); // ++P
    out.push_back(next);
  }
  // precomp now {O, 1P, 2P, 3P, ..., (2^w-1)P} -> size 16 for w = 4

  return out;
}

jcbn_crv_p
windowed_scalar_mul(const std::vector<jcbn_crv_p>& _precomp, const ix& _num, const ix& _p)
{
  jcbn_crv_p Q{j_identity_element};
  std::size_t m = bits_to_represent(_num) / window_size;

  while ((m * window_size) < bits_to_represent(_num))
  {
    ++m;
  }

  for (std::size_t i = 0; i != m; ++i)
  {
    for (auto j = 0ul; j != window_size; ++j)
    {
      Q = point_double(Q, _p);
    }

    const std::size_t start_idx = ((signed)m - (signed)i - 1) * window_size;
    const std::size_t nbits = _num.get_bits(start_idx, window_size);

    if (nbits > 0) [[likely]]
    {
      Q = point_add(Q, _precomp[nbits], _p);
    }
  }
  return Q;
}

/* TODO: 
sign(A-B)
*/

ix determine_group_order(const jcbn_crv_p& _g, const ix& _p)
{
  const auto precomp = precompute(_g, _p);

  ix i = 2;
  while (true)
  {
    const auto current = windowed_scalar_mul(precomp, i, _p);
    if (from_jacobian(current, _p) == from_jacobian(_g,_p))
    {
      return i;
    }
    i=i+1;
  }
  return i -1;
}

ix legendre(const ix& _num, const ix& _p)
{
  const auto ls = _num.pow_mod((_p -1) / 2, _p);
  return ls == _p -1 ? -1 : ls;
}

ix modular_sqrt(const ix& a, const ix& p)
{
  if (legendre(a,p) != 1)
  {
    return 0;
  }
  if (a == 0){
    return 0;
  }
  if (p == 2) {
    return 0;
  }
  if (p % 4 == 3) {
    return a.pow_mod(((p+1) / 4), p);
  }

  auto s= p-1;
  ix e {0};

  while (s % 2 == 0) {
    s = s / 2;
    e = e+1;
  }

  ix n {2};
  while (legendre(n, p) != -1)
  {
    n = n+1;
  }

  auto x = a.pow_mod((s+1)/ 2, p);
  auto b = a.pow_mod(s,p);
  auto g = n.pow_mod(s, p);
  auto r = e;

  while (true) {

    auto t = b;
    ix m = 0;
    
    for (; m < r; m = m +1)
    {
      if (t == 1) {
        break;
      }
      t = t.pow_mod(2,p);
    }

    if (m == 0)
    {
      return x;
    }

    /* TODO: possible bug: 2 ** (r-m-1) shouldnt be powmod */
    auto gs = g.pow_mod(ix{2}.pow_mod(r-m-1, p), p);

    g = (gs * gs) % p;
    x = (x*gs) % p;
    b = (b*g) % p;
    r = m;
  }
  return 0;
}

bool is_on_curve(const crv_p& _point,const ix& _p)
{
  return ((_point.x.pow(3) + 7 - _point.y.pow(2)) % _p) == 0;
}

crv_p curve(const ix& _x, const ix&  _p)
{
  auto p = crv_p{_x, modular_sqrt(_x.pow(3) + 7, _p) % _p};
  return is_on_curve(p, _p) ? p : a_identity_element; 
}

struct mpf_wrap {
  
  mpf_wrap()= default;

  mpf_wrap(const char* _str, int _base)
  {
    fmpz_init(value_);
    fmpz_set_str(value_, _str, _base);
  }
  
  mpf_wrap(const ix& _n)
  {
    fmpz_init(value_);
    fmpz_set_mpz(value_, _n.value_);
  }

  mpf_wrap(const mpf_wrap& _other)
  {
    fmpz_set(value_, _other.value_);
  }

  mpf_wrap& operator=(const mpf_wrap& _other)
  {
    fmpz_set(value_, _other.value_);
    return *this;
  }

  mpf_wrap(mpf_wrap&& _other) noexcept 
  {
    fmpz_set(value_, _other.value_);
  }

  mpf_wrap& operator=(mpf_wrap&& _other) noexcept 
  {
    fmpz_set(value_, _other.value_);
    return *this;
  }

  ~mpf_wrap()
  {
    fmpz_clear(value_);
  }

  fmpz_t value_{};
};

mpf_wrap to_mpf(const ix& _n)
{
  mpf_wrap out("0", 10);
  fmpz_set_mpz(out.value_, _n.value_); 
  return out;
}

/*
  returns point half
  if point is odd returns identity element
*/
crv_p point_half(const crv_p& _original_point, const ix& _mod, fmpz_t modulus)
{
  const ix X_test =_original_point.x;
  const unsigned b_test = 7;

  fmpz_mod_ctx_t field_ctx;
  fmpz_mod_ctx_init(field_ctx, modulus);

  fmpz_mod_poly_t polynomial;
  fmpz_mod_poly_init(polynomial, field_ctx);

  fmpz_mod_poly_set_coeff_fmpz(polynomial, 4, to_mpf(ix{-1}).value_, field_ctx);
  fmpz_mod_poly_set_coeff_fmpz(polynomial, 3, to_mpf(ix{4*X_test}).value_, field_ctx);
  fmpz_mod_poly_set_coeff_fmpz(polynomial, 1, to_mpf(ix{8*b_test}).value_, field_ctx);
  fmpz_mod_poly_set_coeff_fmpz(polynomial, 0, to_mpf(ix{4*b_test*X_test}).value_, field_ctx);

  fmpz_mod_poly_factor_t root;
  fmpz_mod_poly_factor_init(root, field_ctx);
  fmpz_mod_poly_roots(root, polynomial, 0, field_ctx);

  //fmpz_mod_poly_factor_print_pretty(root, "x", field_ctx);
  // std::cout << "\n";

  std::cout << "roots: " << root->num << "\n";

  for (int i = 0; i != root->num; i++)
  {
    const auto curr_poly = root->poly + i;

    fmpz_t out_numfmpz;
    fmpz_mod_poly_evaluate_fmpz(out_numfmpz, curr_poly, to_mpf(0).value_, field_ctx);
    ix final_num;
    fmpz_get_mpz(final_num.value_, out_numfmpz);
    final_num = (-final_num) % _mod;

    auto new_point1 = curve(final_num, _mod);
    const auto double_point1 = from_jacobian(point_double(to_jacobian(new_point1), _mod), _mod);

    if (double_point1 == _original_point)
    {
      fmpz_mod_poly_factor_clear(root, field_ctx);
      fmpz_mod_poly_clear(polynomial, field_ctx);
      fmpz_mod_ctx_clear(field_ctx);
      return new_point1;
    }

    auto new_point2 = crv_p{new_point1.x, _mod - new_point1.y};
    const auto double_point2 = from_jacobian(point_double(to_jacobian(new_point2), _mod), _mod);

    if (double_point2 == _original_point)
    {
      fmpz_mod_poly_factor_clear(root, field_ctx);
      fmpz_mod_poly_clear(polynomial, field_ctx);
      fmpz_mod_ctx_clear(field_ctx);
      return new_point2;
    }
  }

  fmpz_mod_poly_factor_clear(root, field_ctx);
  fmpz_mod_poly_clear(polynomial, field_ctx);
  fmpz_mod_ctx_clear(field_ctx);

  return a_identity_element;
}

struct finite_field
{
  finite_field() = default;

  finite_field(const ix& _modulo) : mod(_modulo)
  {
    fmpz_mod_ctx_init(field_ctx, mod.value_);
  }

  ~finite_field()
  {
    fmpz_mod_ctx_clear(field_ctx);
  }


  fmpz_mod_ctx_t field_ctx{};
  mpf_wrap mod{};
};


struct mpoly_factor 
{
  ix factor{1};
  signed long long exponent{1};

  mpoly_factor friend operator*(const ix& lhs, const mpoly_factor& rhs) 
  {
    return {.factor = lhs, .exponent = rhs.exponent};
  }

  mpoly_factor friend operator^(const mpoly_factor& lhs, signed long long rhs)
  {
    return {.factor = lhs.factor, .exponent = rhs};
  }
};

/* ew a global */
namespace pf {
const static mpoly_factor X{};
}


struct mod_polynomial 
{
  mod_polynomial(const finite_field& _field, std::vector<mpoly_factor>  _factors) 
    : factors(std::move(_factors)), field(_field)
  {
    fmpz_mod_poly_init(polynomial, field.field_ctx);

    for (const auto& factor : factors)
    {
       fmpz_mod_poly_set_coeff_fmpz(polynomial, factor.exponent, to_mpf(factor.factor).value_, field.field_ctx);
    }
  }
    mod_polynomial(const ix& _field_modulo, std::vector<mpoly_factor>  _factors) 
    : factors(std::move(_factors)), field(finite_field{_field_modulo})
  {
    fmpz_mod_poly_init(polynomial, field.field_ctx);

    for (const auto& factor : factors)
    {
       fmpz_mod_poly_set_coeff_fmpz(polynomial, factor.exponent, to_mpf(factor.factor).value_, field.field_ctx);
    }
  }

  [[nodiscard]] std::vector<ix> solve()
  {
    std::vector<ix> out{};
    fmpz_mod_poly_factor_t root;
    fmpz_mod_poly_factor_init(root, field.field_ctx);
    fmpz_mod_poly_roots(root, polynomial, 0,  field.field_ctx);

    for (int i = 0; i != root->num; i++)
    {
      const auto curr_poly = root->poly + i;

      fmpz_t out_numfmpz;
      fmpz_mod_poly_evaluate_fmpz(out_numfmpz, curr_poly, to_mpf(0).value_, field.field_ctx);
      ix final_num;
      fmpz_get_mpz(final_num.value_, out_numfmpz);
      final_num = (-final_num) % ix{field.mod.value_};
      out.push_back(final_num);
    }

    fmpz_mod_poly_factor_clear(root, field.field_ctx);

    return out;
  }

  inline decltype(auto) operator+(const mod_polynomial& other) 
  {
    fmpz_mod_poly_add(polynomial, polynomial, other.polynomial, field.field_ctx);
    return (*this);
  }

  inline decltype(auto) operator-(const mod_polynomial& other) 
  {
    fmpz_mod_poly_sub(polynomial, polynomial, other.polynomial, field.field_ctx);
    return (*this);
  }

  inline decltype(auto) operator*(const mod_polynomial& other) 
  {
    fmpz_mod_poly_mul(polynomial, polynomial, other.polynomial, field.field_ctx);
    return (*this);
  }

  inline decltype(auto) operator/(const mod_polynomial& other) 
  { 
    if (!divided_by(other))
    {
      std::cout << "!!! WARNING !!! trying to divide non divisible polynomial!\n";
      assert(false);
    }

    fmpz_mod_poly_div(polynomial, polynomial, other.polynomial, field.field_ctx);
    return (*this);
  }

  inline decltype(auto) factorize()
  {
    fmpz_mod_poly_factor_t fac;
    fmpz_mod_poly_factor_init(fac, field.field_ctx);
    fmpz_mod_poly_factor(fac, polynomial, field.field_ctx);
    fmpz_mod_poly_factor_clear(fac, field.field_ctx);
    return (*this);
  }

  [[nodiscard]] bool divided_by(const mod_polynomial& other) const
  {
    fmpz_mod_poly_t dummy;
    fmpz_mod_poly_init(dummy, field.field_ctx);
    return (bool)fmpz_mod_poly_divides(dummy, polynomial, other.polynomial, field.field_ctx);
  }

  void print()
  {
    fmpz_mod_poly_print_pretty(polynomial,"X", field.field_ctx);
    std::puts("");
  }

  fmpz_mod_poly_t polynomial{};

  std::vector<mpoly_factor> factors;
  finite_field field;
};

crv_p subtract_by_one(const std::vector<jcbn_crv_p>& _precomp, const crv_p& _point, const ix& _h, const ix& _p) 
{
  return from_jacobian(point_add(to_jacobian(_point), windowed_scalar_mul(_precomp, _h-1, _p), _p), _p);
}

ix solving_the_ecdlp(const std::vector<jcbn_crv_p>& _precomp, const crv_p& _point, const crv_p& _generator_point, const ix& _h ,const ix& _p, fmpz_t stupi_mod)
{
  ix out{0};
  crv_p  point = _point;

  while (point != _generator_point)
  {
    std::cout << "point: ";
    point.print();

    auto half_p = point_half(point, _p, stupi_mod);
    
    std::cout << "half_p: ";
    half_p.print();

    if (half_p == a_identity_element)
    { 
      out = out + 1;

      point = subtract_by_one(_precomp, point, _h, _p);
      half_p = point_half(point, _p, stupi_mod);
        
      std::cout << "point after: ";
      point.print();
      std::cout << "half_p after: ";
      half_p.print();

      assert(half_p != a_identity_element);
    }

    out = out * 2;

    auto out2 = out;
    out2.reverse();

    std::cout << "out: " << out2 << "\n";
    point = half_p;
    sleep(1);
  }

  out.reverse();
  return out;
}

int
main()
{
  mod_polynomial p{17, {2*pf::X^2, 4*pf::X^4}};
  mod_polynomial q{17, {pf::X^2}};

  p.print();
  q.print();

  auto solve = p.solve();

  std::cout << "solutions: \n";
  for (const auto& ite : solve)
  {
    std::cout << "  "<< ite << "\n";
  }

  std::cout << std::boolalpha << p.divided_by(q) << "\n";

  p = p/q;

  p.print();

  p.factorize();
  
  solve = p.solve();

  std::cout << "solutions: \n";
  for (const auto& ite : solve)
  {
    std::cout << "  "<< ite << "\n";
  }
  p.print();

  return 0;

  //ix mod_global = "115792089237316195423570985008687907853269984665640564039457584007908834671663";
  //crv_p G = {"55066263022277343669578718895168534326250603453777594175500187360389116729240",
  //            "32670510020758816978083085130507043184471273380659243275938904335757337482424"};
  //ix privKeyA = "40505654708211189456746820883201845994248137211058198699828051064905928553035";
  //ix privKeyB = "83862260130769358743610306176715755043868098730045613807339143668249321773381";
  //const auto G_precomp = precompute(to_jacobian(G), mod_global);
  //fmpz_t modulus;
  //fmpz_init(modulus);
  //fmpz_set_str(modulus, "115792089237316195423570985008687907853269984665640564039457584007908834671663", 10);
  //ix n = "115792089237316195423570985008687907852837564279074904382605163141518161494337";

  ix mod_global = "17";
  crv_p G = {"15",
              "13"};
  ix privKeyA = "4";
  ix privKeyB = "34";
  const auto G_precomp = precompute(to_jacobian(G), mod_global);
  fmpz_t modulus;
  fmpz_init(modulus);
  fmpz_set_str(modulus, "17", 10);
  ix n = "18";

  crv_p p_2G = from_jacobian(point_double(to_jacobian(G), mod_global), mod_global); 
  auto p_3G = point_add(to_jacobian(G), to_jacobian(p_2G), mod_global);

  for (int i = 3; i <= 20; i+=2)
  {
    std::cout << i << "G: ";
    from_jacobian(p_3G, mod_global).print();
    auto half_thingy =  point_half(from_jacobian(p_3G, mod_global), mod_global, modulus);
    std::cout << "half point: ";
    half_thingy.print();
    p_3G = point_add(p_3G, to_jacobian(p_2G), mod_global);
  }

  std::cout << "--------------------------- even ----------------------------\n";

  auto p_2G2 = p_2G;

  for (int i = 2; i <= 20; i+=2)
  {
    std::cout << i << "G: ";
    p_2G2.print();
    auto half_thingy =  point_half(p_2G2, mod_global, modulus);
    std::cout << "half point: ";
    half_thingy.print();
    p_2G2 = from_jacobian(point_add(to_jacobian(p_2G2), to_jacobian(p_2G), mod_global), mod_global);
  }

  return 0;

  p_2G.print();


  // original point:        55066263022277343669578718895168534326250603453777594175500187360389116729240
  // double point halfed:   55066263022277343669578718895168534326250603453777594175500187360389116729240

  auto half2G = point_half(p_2G, mod_global, modulus);

  std::cout << "\n";

  half2G.print();

  G.print();


  jcbn_crv_p pubKeyA = windowed_scalar_mul(G_precomp, privKeyA, mod_global);
  jcbn_crv_p pubKeyB = windowed_scalar_mul(G_precomp, privKeyB, mod_global);

  std::cout << "--------- pubkeys ---------\n";
  from_jacobian(pubKeyA, mod_global).print();
  from_jacobian(pubKeyB, mod_global).print();
  std::cout << "---------------------------\n";

  std::cout << solving_the_ecdlp(G_precomp, from_jacobian(pubKeyA, mod_global), G, n, mod_global, modulus);
  std::cout << solving_the_ecdlp(G_precomp, from_jacobian(pubKeyB, mod_global), G, n, mod_global, modulus);


  // const jcbn_crv_p pubKeyAJ = pubKeyA;
  // const jcbn_crv_p pubKeyBJ = pubKeyB;

  // const auto precomp = precompute(pubKeyBJ, mod_global);
  // const auto precomp2 = precompute(pubKeyAJ, mod_global);

  // jcbn_crv_p shared_secretAJ, shared_secretBJ;

  // std::cout << "jacobian windowed: \n";
  // {
  //   perf_ _("jacobian windowed");

  //   shared_secretAJ = windowed_scalar_mul(precomp, privKeyA, mod_global);
  //   shared_secretBJ = windowed_scalar_mul(precomp2, privKeyB, mod_global);
  // }
  
  // from_jacobian(shared_secretAJ, mod_global).print();
  // from_jacobian(shared_secretBJ, mod_global).print();

  // return 0;
}

// here be dragons!

