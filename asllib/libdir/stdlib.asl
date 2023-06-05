//------------------------------------------------------------------------------
//
//                             ASL standard lib
//
//-----------------------------------------------------------------------------


//------------------------------------------------------------------------------
// Externals

// Replicate
// BitCount
// LowerSetBit
// UInt
// SInt

//------------------------------------------------------------------------------
// Standard integer functions and procedures (§9.1)

// SInt
// UInt

func Min(a :: integer, b :: integer) => integer
begin
  return if a < b then a else b;
end

func Max(a :: integer, b :: integer) => integer
begin
  return if a > b then a else b;
end

func Abs(x :: integer) => integer
begin
  return if x < 0 then -x else x;
end

// Log2


//------------------------------------------------------------------------------
// Functions on reals (TODO, §9.2)

//------------------------------------------------------------------------------
// Standard bitvector functions and procedures

// For most of these functions, some implicitely dependently typed version
// exists in the specification. We do not yet support those.

// Externals
// Replicate
// BitCount
// LowerSetBit
// HigherSetBit

func Len{N}(x :: bits(N)) => integer
begin
  return N;
end

func Zeros(n :: integer) => bits(n)
begin
  return Replicate ('0', n);
end

func Ones(n :: integer) => bits(n)
begin
  return Replicate ('1', n);
end

func IsZero(x :: bits(n)) => boolean
begin
  return BitCount(x) == 0;
end

func IsOnes{N}(x :: bits(N)) => boolean
begin
  return x == Ones(N);
end

func SignExtend(x::bits(M), N::integer) => bits(N)
begin
  return [Replicate(x[M-1], N - M), x];
end

func ZeroExtend(x :: bits(M), N::integer) => bits(N)
begin
  return [Zeros(N - M), x];
end

func Extend(x :: bits(M), N :: integer, unsigned::boolean) => bits(N)
begin
  return if unsigned then ZeroExtend(x, N) else SignExtend(x, N);
end

func CountLeadingZeroBits{N}(x :: bits(N)) => integer
begin
  return N - 1 - HighestSetBit(x);
end

// Leading sign bits in a bitvector. Count the number of consecutive
// bits following the leading bit, that are equal to it.
func CountLeadingSignBits{N}(x::bits(N)) => integer{0..N}
begin
  return CountLeadingZeroBits(x[N-1:1] EOR x[N-2:0]);
end

// Treating input as an integer, align down to nearest multiple of 2^y.
func AlignDown{N}(x:: bits(N), y:: integer{1..N}) => bits(N)
begin
    return [x[N-1,N-y], Zeros(y)];
end

// Treating input as an integer, align up to nearest multiple of 2^y.
// Returns zero if the result is not representable in N bits.
func AlignUp{N}(x::bits(N), y::integer{1..N}) => bits(N)
begin
  if IsZero(x[y-1:0]) then
    return x;
  else
    return [x[N-1:y]+1, Zeros(y)];
  end
end

func LSL_C(x :: bits(N), shift :: integer) => (bits(N), bit)
begin
  assert shift > 0 && shift < 256;
  extended_x = [x, Zeros(shift)];
  result = extended_x[N-1:0];
  carry_out = extended_x[N];
  return (result, carry_out);
end

func LSL(x :: bits(N), shift :: integer) => bits(N)
begin
  assert shift >= 0;
  if shift == 0 then
    return x;
  else
    let (result, -) = LSL_C(x, shift);
    return result;
  end
end

func LSR_C(x :: bits(N), shift :: integer) => (bits(N), bit)
begin
  assert shift > 0 && shift < 256;
  extended_x = ZeroExtend(x, shift+N);
  result = extended_x[shift+N-1 : shift];
  carry_out = extended_x[shift-1];
  return (result, carry_out);
end

func LSR(x :: bits(N), shift :: integer) => bits(N)
begin
  assert shift >= 0;
  if shift == 0 then
    return x;
  else
    let (result, -) = LSR_C(x, shift);
    return result;
  end
end

func ASR_C(x :: bits(N), shift :: integer) => (bits(N), bit)
begin
  assert shift > 0 && shift < 256;
  extended_x = SignExtend(x, shift+N);
  result = extended_x[shift+N-1:shift];
  carry_out = extended_x[shift-1];
  return (result, carry_out);
end

func ASR(x :: bits(N), shift :: integer) => bits(N)
begin
  assert shift >= 0;
  if shift == 0 then
    return x;
  else
    let (result, -) = ASR_C(x, shift);
    return result;
  end
end

func ROR_C(x :: bits(N), shift :: integer) => (bits(N), bit)
begin
  assert shift != 0 && shift < 256;
  m = shift MOD N;
  result = LSR(x,m) OR LSL(x,N-m);
  carry_out = result[N-1];
  return (result, carry_out);
end

func ROR(x :: bits(N), shift :: integer) => bits(N)
begin
  assert shift >= 0;
  if shift == 0 then
    return x;
  else
    let (result, -) = ROR_C(x, shift);
    return result;
  end
end

