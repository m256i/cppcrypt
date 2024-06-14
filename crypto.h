#pragma once

#include "gmpxx.h"

#include <algorithm>
#include <cassert>
#include <cstddef>
#include <flint/flint.h>
#include <flint/fmpz.h>
#include <gmp.h>
#include <iostream>

// TODO: possible performance improvements can be done in this file

namespace blue_crypto
{

class GmpWrapper
{
public:
  // Constructors
  GmpWrapper() { mpz_init(value_); }

  GmpWrapper(const char* str)
  {
    if (str[0] == '0' && str[1] == 'x')
    {
      mpz_init_set_str(value_, str + 2, 16);
    }
    else
    {
      mpz_init_set_str(value_, str, 10);
    }
  }

  GmpWrapper(const char* str, int base)
  {
    mpz_init_set_str(value_, str + 2, base);
  }

  GmpWrapper(const GmpWrapper& other) { mpz_init_set(value_, other.value_); }
  GmpWrapper(int intValue) { mpz_init_set_si(value_, intValue); }

  GmpWrapper(fmpz_t fmp)
  {
    mpz_init(value_);
    fmpz_get_mpz(value_, fmp);
  }

  // Destructor
  ~GmpWrapper() { mpz_clear(value_); }

  void reverse()
  {
    std::string str = mpz_get_str(nullptr, 2, value_);
    std::reverse(str.begin(), str.end());
    mpz_init_set_str(value_, str.data(), 2);
  }

  // Assignment operator
  GmpWrapper&
  operator=(const GmpWrapper& other)
  {
    if (this != &other)
    {
      mpz_set(value_, other.value_);
    }
    return *this;
  }

  // Arithmetic operators
  GmpWrapper
  operator+(const GmpWrapper& other) const
  {
    GmpWrapper result;
    mpz_add(result.value_, value_, other.value_);
    return result;
  }

  GmpWrapper
  operator-(const GmpWrapper& other) const
  {
    GmpWrapper result;
    mpz_sub(result.value_, value_, other.value_);
    return result;
  }

  GmpWrapper
  operator*(const GmpWrapper& other) const
  {
    GmpWrapper result;
    mpz_mul(result.value_, value_, other.value_);
    return result;
  }

  GmpWrapper
  operator%(const GmpWrapper& other) const
  {
    GmpWrapper result;
    mpz_mod(result.value_, value_, other.value_);
    return result;
  }

  GmpWrapper
  operator/(const GmpWrapper& other) const
  {
    if (other == 0)
    {
      // Handle division by zero
      throw std::invalid_argument("Division by zero");
    }

    GmpWrapper result;
    mpz_tdiv_q(result.value_, value_, other.value_);
    return result;
  }

  // Bitwise AND operator
  GmpWrapper
  operator&(const GmpWrapper& other) const
  {
    GmpWrapper result;
    mpz_and(result.value_, value_, other.value_);
    return result;
  }

  // Bitwise OR operator
  GmpWrapper
  operator|(const GmpWrapper& other) const
  {
    GmpWrapper result;
    mpz_ior(result.value_, value_, other.value_);
    return result;
  }

  // Bitwise XOR operator
  GmpWrapper
  operator^(const GmpWrapper& other) const
  {
    GmpWrapper result;
    mpz_xor(result.value_, value_, other.value_);
    return result;
  }

  // Bitwise NOT operator
  GmpWrapper
  operator~() const
  {
    GmpWrapper result;
    mpz_com(result.value_, value_);
    return result;
  }

  [[nodiscard]] GmpWrapper
  pow(unsigned int exp) const
  {
    GmpWrapper result;
    mpz_pow_ui(result.value_, value_, exp);
    return result;
  }


  [[nodiscard]] GmpWrapper
  pow_mod(const GmpWrapper& _exp, const GmpWrapper& _mod) const
  {
    GmpWrapper result;
    mpz_powm (result.value_, value_,_exp.value_, _mod.value_);
    return result;
  }

  [[nodiscard]] GmpWrapper
  pow_mod(const long unsigned _exp, const GmpWrapper& _mod) const
  {
    GmpWrapper result;
    mpz_powm_ui  (result.value_, value_,_exp , _mod.value_);
    return result;
  }

  unsigned long to_int()
  {
    return mpz_get_ui(value_); 
  }

  [[nodiscard]] unsigned char
  get_bit(size_t bitIndex) const
  {
    if (bitIndex >= bitlength())
    {
      return 0;
    }

    return mpz_tstbit(value_, bitIndex);
  }

  [[nodiscard]] std::size_t
  get_bits(std::size_t start_bit, std::size_t num_bits) const
  {
    std::size_t out{0};

    for (std::size_t i = 0; i != num_bits; i++)
    {
      out |= (get_bit(start_bit + i) << (i));
    }

    return out;
  }

  size_t
  count_trailing_zeros() const
  {
    return static_cast<size_t>(mpz_scan1(value_, 0));
  }

  size_t
  bitlength() const
  {
    return static_cast<size_t>(mpz_sizeinbase(value_, 2));
  }

  void
  write() const
  {
    char* str = mpz_get_str(nullptr, 10, value_);
    std::cout << str;
    free(str);
  }

  void
  writeb() const
  {
    char* str = mpz_get_str(nullptr, 2, value_);
    std::cout << str;
    free(str);
  }

  // Equality operator
  bool
  operator==(const GmpWrapper& other) const
  {
    return mpz_cmp(value_, other.value_) == 0;
  }

  // Inequality operator
  bool
  operator!=(const GmpWrapper& other) const
  {
    return mpz_cmp(value_, other.value_) != 0;
  }

  // Less than operator
  bool
  operator<(const GmpWrapper& other) const
  {
    return mpz_cmp(value_, other.value_) < 0;
  }

  // Less than or equal to operator
  bool
  operator<=(const GmpWrapper& other) const
  {
    return mpz_cmp(value_, other.value_) <= 0;
  }

  // Greater than operator
  bool
  operator>(const GmpWrapper& other) const
  {
    return mpz_cmp(value_, other.value_) > 0;
  }

  // Greater than or equal to operator
  bool
  operator>=(const GmpWrapper& other) const
  {
    return mpz_cmp(value_, other.value_) >= 0;
  }

  // Addition with int
  GmpWrapper
  operator+(int intValue) const
  {
    GmpWrapper n(intValue);
    return this->operator+(n);
  }

  // Subtraction with int
  GmpWrapper
  operator-(int intValue) const
  {
    GmpWrapper n(intValue);
    return this->operator-(n);
  }

  GmpWrapper
  operator-() const
  {
    GmpWrapper result;
    mpz_neg(result.value_, value_);
    return result;
  }

  // Multiplication with int
  GmpWrapper
  operator*(int intValue) const
  {
    GmpWrapper result;
    mpz_mul_si(result.value_, value_, intValue);
    return result;
  }

  // Division with int
  GmpWrapper
  operator/(int intValue) const
  {
    if (intValue == 0)
    {
      // Handle division by zero
      throw std::invalid_argument("Division by zero");
    }

    GmpWrapper n(intValue);
    return this->operator/(n);
  }

  // Output operator
  friend std::ostream&
  operator<<(std::ostream& os, const GmpWrapper& gmp)
  {
    return os << mpz_get_str(nullptr, 10, gmp.value_);
  }

  friend GmpWrapper
  operator*(int lhs, const GmpWrapper& gmp)
  {
    GmpWrapper n(lhs);
    return n * gmp;
  }

  friend GmpWrapper
  operator+(int lhs, const GmpWrapper& gmp)
  {
    GmpWrapper n(lhs);
    return n + gmp;
  }

  mpz_t value_{};
};

} // namespace blue_crypto

blue_crypto::GmpWrapper operator ""_n10(const char* _str)
{
  return {_str, 10};
}

blue_crypto::GmpWrapper operator ""_n16(const char* _str)
{
  return {_str, 16};
}
