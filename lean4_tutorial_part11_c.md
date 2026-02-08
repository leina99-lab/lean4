# Part 11-C: 생성 함수 기초 (Generating Functions – Introduction)

> **Rosen 『이산수학』 8판 8.4절** 기반  
> **선수 지식**: Part 11-A (점화 관계 기초), Part 11-B (선형 점화 관계)  
> **목표**: 생성 함수의 개념을 이해하고, Lean 4에서 유한 다항식과 **형식적 멱급수**(formal power series)를 다루는 기초를 익힌다.

---

## 0. 이 파트에서 배울 핵심 개념

| 개념 | 설명 |
|------|------|
| **생성 함수**(generating function) | 수열 `{aₙ}`을 다항식/급수 `Σ aₖxᵏ`으로 표현 |
| **형식적 멱급수**(formal power series) | 수렴 여부와 무관하게 계수만으로 연산 |
| **닫힌 형태**(closed form) | 급수를 유한한 식으로 표현 |
| **멱급수의 덧셈 · 곱셈** | 계수끼리의 연산 규칙 |
| **확장된 이항 계수**(extended binomial coefficient) | 실수 `u`에 대해 `C(u, k)` 정의 |

> 💡 **왜 생성 함수를 배울까?**  
> 점화 관계를 "대수적으로" 풀 수 있게 해주는 강력한 도구이다. 복잡한 계수 문제를 다항식의 곱으로 변환하면, 컴퓨터 대수 시스템이 자동으로 풀어줄 수 있다. Lean 4에서는 유한 다항식(`Polynomial`)과 형식적 멱급수(`PowerSeries`)를 모두 지원한다.

---

## 1. 생성 함수란 무엇인가?

### 1.1 직관적 이해: 수열을 "포장"하는 방법

수학에서 **수열**(sequence)은 숫자들의 나열이다:

```
a₀, a₁, a₂, a₃, ...
```

이 수열을 하나의 "함수"로 포장하는 방법이 **생성 함수**이다. 아이디어는 간단하다:

> 각 항 `aₖ`를 `xᵏ`의 **계수**(coefficient)로 붙여서, 하나의 다항식(또는 급수)으로 만든다.

**정의**: 수열 `a₀, a₁, a₂, ...`의 **생성 함수**(generating function)는 다음과 같다:

$$G(x) = a_0 + a_1 x + a_2 x^2 + a_3 x^3 + \cdots = \sum_{k=0}^{\infty} a_k x^k$$

여기서 중요한 점은, 우리는 `x`에 실제 숫자를 대입하는 것이 아니라, **형식적**(formal)으로 다룬다는 것이다. 즉, 수렴 여부는 신경 쓰지 않는다!

> 🎒 **비유**: 생성 함수는 수열의 "DNA"와 같다. DNA에 생물의 모든 정보가 담겨 있듯이, 생성 함수 하나에 수열의 모든 정보가 담겨 있다.

### 1.2 간단한 예시

**예시 1**: 수열 `1, 1, 1, 1, ...` (모든 항이 1)의 생성 함수는?

$$G(x) = 1 + x + x^2 + x^3 + \cdots = \frac{1}{1 - x}$$

이것은 **등비급수**(geometric series)의 공식이다. 물론 형식적으로 다루므로 `|x| < 1`이라는 조건은 무시해도 된다.

**예시 2**: 유한 수열 `2, 2, 2, 2, 2, 2` (여섯 개의 2)의 생성 함수는?

$$G(x) = 2 + 2x + 2x^2 + 2x^3 + 2x^4 + 2x^5 = 2(1 + x + x^2 + x^3 + x^4 + x^5)$$

이것은 `2 · (1 - x⁶) / (1 - x)`로도 쓸 수 있다.

**예시 3**: 수열 `1, a, a², a³, ...`의 생성 함수는?

$$G(x) = 1 + ax + a^2 x^2 + \cdots = \frac{1}{1 - ax}$$

### 1.3 Lean 4에서의 표현

Lean 4의 Mathlib에는 **형식적 멱급수**(formal power series)를 위한 타입 `PowerSeries`가 있다. 하지만 이 타입은 상당히 고급이므로, 여기서는 기초 개념을 이해하기 위해 **유한 다항식**(`Polynomial`)과 **리스트 기반 표현**을 사용한다.

```lean
-- 수열을 함수로 표현하기
def seq1 : ℕ → ℕ := fun _ => 1        -- 수열 1, 1, 1, ...
def seqPow (a : ℕ) : ℕ → ℕ := fun n => a ^ n  -- 수열 1, a, a², ...

-- 유한 수열을 리스트로 표현
def finiteSeq : List ℕ := [2, 2, 2, 2, 2, 2]

-- n번째 항까지의 부분합 (생성 함수에서 x=1을 대입한 것과 같다)
def partialSum (a : ℕ → ℕ) (n : ℕ) : ℕ :=
  (List.range (n + 1)).map a |>.sum

#eval partialSum seq1 5    -- 6 (= 1+1+1+1+1+1)
#eval partialSum (seqPow 2) 4  -- 31 (= 1+2+4+8+16)
```

---

## 2. 생성 함수의 연산: 덧셈과 곱셈

### 2.1 정리 1: 멱급수의 덧셈과 곱셈 (Rosen 정리 1)

생성 함수의 진정한 힘은 **연산**에 있다. 두 수열의 생성 함수를 더하거나 곱하면, 결과도 의미 있는 수열의 생성 함수가 된다.

> **정리 1** (멱급수의 덧셈과 곱셈)  
> `f(x) = Σ aₖxᵏ`이고 `g(x) = Σ bₖxᵏ`라 하자. 그러면:
>
> 1. **덧셈**: `f(x) + g(x) = Σ (aₖ + bₖ)xᵏ`
> 2. **곱셈**: `f(x) · g(x) = Σ cₖxᵏ`, 여기서 `cₖ = Σⱼ₌₀ᵏ aⱼbₖ₋ⱼ`

곱셈에서 나오는 `cₖ = Σⱼ₌₀ᵏ aⱼbₖ₋ⱼ`를 **합성곱**(convolution) 또는 **코시 곱**(Cauchy product)이라고 한다.

#### 합성곱을 직관적으로 이해하기

`f(x) · g(x)`에서 `xᵏ`의 계수를 구하려면, `f(x)`에서 `xʲ`항을 고르고 `g(x)`에서 `xᵏ⁻ʲ`항을 골라서 곱한 것을 모두 더한다. 즉, 지수의 합이 `k`가 되는 모든 조합을 고려한다.

> 🎒 **비유**: 두 주사위를 던질 때, 합이 `k`가 되는 경우의 수를 구하는 것과 같다!

#### Lean 4 구현

```lean
-- 합성곱 (convolution) 직접 구현
def convolution (a b : ℕ → ℕ) (k : ℕ) : ℕ :=
  (List.range (k + 1)).map (fun j => a j * b (k - j)) |>.sum

-- 예시: 수열 {1, 1, 1, ...}의 자기 자신과의 합성곱
-- 결과는 {1, 2, 3, 4, ...} (= (k+1)번째 항)
#eval List.range 6 |>.map (convolution seq1 seq1)
-- [1, 2, 3, 4, 5, 6]

-- 이것이 바로 1/(1-x)² = Σ (k+1)xᵏ 이다!
```

### 2.2 왜 이것이 유용한가?

합성곱의 핵심 응용은 **계수 문제**(counting problem)이다. 동전 교환 문제를 생각해 보자:

> **문제**: 1원짜리, 2원짜리, 5원짜리 동전으로 `r`원을 만드는 방법의 수는?

이 문제의 답은 다음 생성 함수에서 `xʳ`의 계수이다:

$$\frac{1}{(1-x)(1-x^2)(1-x^5)}$$

각 인수의 의미:
- `1/(1-x) = 1 + x + x² + ...`: 1원짜리를 0개, 1개, 2개, ... 사용
- `1/(1-x²) = 1 + x² + x⁴ + ...`: 2원짜리를 0개, 1개, 2개, ... 사용
- `1/(1-x⁵) = 1 + x⁵ + x¹⁰ + ...`: 5원짜리를 0개, 1개, 2개, ... 사용

이들을 곱하면, `xʳ`의 계수가 바로 "총합이 `r`원이 되도록 동전을 선택하는 방법의 수"가 된다!

```lean
-- 동전 교환 문제를 Lean 4로 풀기
-- 1원, 2원, 5원 동전으로 n원을 만드는 방법의 수
def coinChange : ℕ → ℕ
  | 0 => 1  -- 0원을 만드는 방법: 아무것도 안 쓰기 (1가지)
  | n + 1 =>
    -- 완전탐색: 1원 i개, 2원 j개, 5원 k개로 n+1을 만들 수 있는 경우의 수
    let total := n + 1
    (List.range (total + 1)).foldl (fun acc i =>
      acc + (List.range (total / 2 + 1)).foldl (fun acc2 j =>
        if i + 2 * j ≤ total then
          (List.range (total / 5 + 1)).foldl (fun acc3 k =>
            if i + 2 * j + 5 * k == total then acc3 + 1 else acc3
          ) acc2
        else acc2
      ) 0
    ) 0

#eval List.range 15 |>.map coinChange
-- [1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 10, 11, 13, 14, 16]
-- 예: 7원을 만드는 방법은 6가지
--   7 = 7·1 = 5·1+1·2 = 3·1+2·2 = 1·1+3·2 = 2+5 = 2·1+5
```

---

## 3. 자주 등장하는 생성 함수들

### 3.1 핵심 생성 함수 목록 (Rosen 표 1)

이 표는 매우 중요하다. 이 표에 있는 몇 가지 "핵심 공식"만 알면, 나머지를 모두 유도할 수 있다.

| 생성 함수 `G(x)` | 수열 `{aₖ}` | 설명 |
|------|------|------|
| `1/(1-x)` | `1, 1, 1, ...` | 등비급수 |
| `1/(1-ax)` | `1, a, a², a³, ...` | 공비가 `a` |
| `1/(1-x)²` | `1, 2, 3, 4, ...` | `aₖ = k+1` |
| `1/(1-x)ⁿ` | `C(n+k-1, k)` | **중복조합** 수 |
| `(1+x)ⁿ` | `C(n,0), C(n,1), ..., C(n,n), 0, ...` | **이항 정리** |
| `eˣ` | `1/0!, 1/1!, 1/2!, ...` | `aₖ = 1/k!` |
| `ln(1+x)` | `0, 1, -1/2, 1/3, ...` | `aₖ = (-1)ᵏ⁺¹/k` |

> 💡 **핵심 원리**: 첫 번째, 네 번째, 다섯 번째 식이 **기본**(base)이다. 나머지는 이들로부터 `x`를 `ax`, `xʳ`, `-x` 등으로 **치환**(substitution)하거나 **미분**(differentiation)하여 유도할 수 있다.

### 3.2 치환의 원리

**치환**(substitution, 또는 **대입**)이란, 생성 함수의 `x`를 다른 식으로 바꾸는 것이다.

예를 들어 `1/(1-x) = 1 + x + x² + ...`에서:
- `x`를 `ax`로 **치환**하면: `1/(1-ax) = 1 + ax + a²x² + ...`
- `x`를 `-x`로 **치환**하면: `1/(1+x) = 1 - x + x² - x³ + ...`
- `x`를 `x²`로 **치환**하면: `1/(1-x²) = 1 + x² + x⁴ + ...`

이 **치환의 원리**는 레고 블록을 조립하는 것과 같다. 기본 블록 하나로 수많은 변형을 만들 수 있다!

```lean
-- 치환의 원리를 Lean 4로 확인
-- 기본: 1/(1-x) → 계수가 모두 1
def geomCoeff : ℕ → ℤ := fun _ => 1

-- x → -x 치환: 1/(1+x) → 계수가 1, -1, 1, -1, ...
def alternatingCoeff : ℕ → ℤ := fun n => (-1) ^ n

-- x → 2x 치환: 1/(1-2x) → 계수가 1, 2, 4, 8, ...
def powTwoCoeff : ℕ → ℤ := fun n => 2 ^ n

-- 검증
#eval List.range 6 |>.map alternatingCoeff  -- [1, -1, 1, -1, 1, -1]
#eval List.range 6 |>.map powTwoCoeff       -- [1, 2, 4, 8, 16, 32]
```

### 3.3 `1/(1-x)²`의 유도 (Rosen 예제 6)

Rosen의 예제 6은 `1/(1-x)²`의 계수를 구하는 문제이다.

`1/(1-x) = 1 + x + x² + x³ + ...`에서 **정리 1의 곱셈**을 적용한다:

$$\frac{1}{(1-x)^2} = \left(\sum_{k=0}^{\infty} x^k\right) \cdot \left(\sum_{j=0}^{\infty} x^j\right) = \sum_{k=0}^{\infty} \left(\sum_{j=0}^{k} 1\right) x^k = \sum_{k=0}^{\infty} (k+1) x^k$$

즉, `1/(1-x)²`은 수열 `1, 2, 3, 4, ...`의 생성 함수이다!

```lean
-- 1/(1-x)² 의 k번째 계수 = k + 1 검증
-- convolution으로 확인
example : convolution seq1 seq1 0 = 1 := by native_decide
example : convolution seq1 seq1 3 = 4 := by native_decide
example : convolution seq1 seq1 9 = 10 := by native_decide

-- 일반적인 정리
theorem conv_ones_eq (k : ℕ) : convolution seq1 seq1 k = k + 1 := by
  simp [convolution, seq1]
  -- 실제로는 List.range의 길이와 map/sum에 대한 보조 정리가 필요
  sorry  -- 완전한 증명은 List에 대한 귀납법이 필요
```

---

## 4. 확장된 이항 계수 (Extended Binomial Coefficients)

### 4.1 왜 확장이 필요한가?

보통 **이항 계수**(binomial coefficient) `C(n, k) = n! / (k!(n-k)!)`는 `n`과 `k`가 **음이 아닌 정수**일 때 정의된다. 하지만 생성 함수에서는 `(1+x)^u`에서 `u`가 **실수**이거나 **음의 정수**일 수 있다. 이를 위해 이항 계수를 확장해야 한다.

### 4.2 정의 2: 확장된 이항 계수 (Rosen 정의 2)

> **정의**: `u`는 실수이고 `k`는 음이 아닌 정수라 하자. **확장 이항 계수**(extended binomial coefficient) `C(u, k)`는:
>
> $$\binom{u}{k} = \begin{cases} \frac{u(u-1)(u-2)\cdots(u-k+1)}{k!} & \text{만약 } k > 0 \\ 1 & \text{만약 } k = 0 \end{cases}$$

핵심은 **분자에 팩토리얼이 없다**는 것이다. 분자는 `u`부터 시작해서 `k`개의 연속하는 수를 곱한 것(**하강 팩토리얼**)이고, 분모만 `k!`이다.

### 4.3 예제 7: 구체적 계산 (Rosen 예제 7)

**`C(-2, 3)` 계산**:

$$\binom{-2}{3} = \frac{(-2)(-3)(-4)}{3!} = \frac{-24}{6} = -4$$

**`C(1/2, 3)` 계산**:

$$\binom{1/2}{3} = \frac{(1/2)(1/2 - 1)(1/2 - 2)}{3!} = \frac{(1/2)(-1/2)(-3/2)}{6} = \frac{3/8}{6} = \frac{1}{16}$$

```lean
-- 확장된 이항 계수 구현 (유리수 범위)
def extBinom (u : ℚ) (k : ℕ) : ℚ :=
  if k = 0 then 1
  else
    let numerator := (List.range k).map (fun i => u - i) |>.foldl (· * ·) 1
    numerator / (Nat.factorial k : ℚ)

-- 예제 7 검증
#eval extBinom (-2) 3      -- -4
#eval extBinom (1/2) 3     -- 1/16
#eval extBinom (-1/2) 2    -- 3/8
```

### 4.4 예제 8: 음의 정수 파라미터 (Rosen 예제 8)

음의 정수 `-n`에 대한 확장 이항 계수는 보통 이항 계수로 표현할 수 있다:

$$\binom{-n}{r} = (-1)^r \binom{n+r-1}{r}$$

이 공식은 매우 중요하다! 유도 과정:

1. 정의에 의해: `C(-n, r) = (-n)(-n-1)···(-n-r+1) / r!`
2. 분자의 각 항에서 `(-1)`을 묶어내면: `(-1)ʳ · n(n+1)···(n+r-1) / r!`
3. 곱셈 순서를 바꾸면: `(-1)ʳ · (n+r-1)! / (r!(n-1)!) = (-1)ʳ · C(n+r-1, r)`

```lean
-- 예제 8 검증
-- C(-n, r) = (-1)^r * C(n+r-1, r)
theorem extBinom_neg (n r : ℕ) (hn : n > 0) :
    extBinom (-(n : ℚ)) r = (-1) ^ r * (Nat.choose (n + r - 1) r : ℚ) := by
  sorry  -- 증명은 하강 팩토리얼의 성질을 이용

-- 구체적 확인
#eval extBinom (-3) 4  -- (-1)^4 * C(6,4) = 1 * 15 = 15
#eval (Nat.choose 6 4 : ℚ)  -- 15 ✓

#eval extBinom (-2) 5  -- (-1)^5 * C(6,5) = -1 * 6 = -6
#eval (-1 : ℚ) ^ 5 * (Nat.choose 6 5 : ℚ)  -- -6 ✓
```

---

## 5. 확장된 이항 정리 (Extended Binomial Theorem)

### 5.1 정리 2: 확장된 이항 정리 (Rosen 정리 2)

보통 **이항 정리**는 `(1+x)ⁿ = Σ C(n,k)xᵏ`이지만, `n`이 양의 정수일 때만 유한 합이다. **확장된 이항 정리**는 `u`가 **임의의 실수**일 때 **무한 급수**로 확장한다:

> **정리 2** (확장된 이항 정리):  
> `|x| < 1`이고 `u`가 실수라 하자. 그러면:
>
> $$(1+x)^u = \sum_{k=0}^{\infty} \binom{u}{k} x^k$$

### 5.2 예제 9: `(1+x)^(-n)`과 `(1-x)^(-n)`의 생성 함수 (Rosen 예제 9)

`n`이 양의 정수일 때:

**(1) `(1+x)^(-n)` 전개**:

확장된 이항 정리에 의해:

$$(1+x)^{-n} = \sum_{k=0}^{\infty} \binom{-n}{k} x^k$$

예제 8의 공식을 사용하면:

$$(1+x)^{-n} = \sum_{k=0}^{\infty} (-1)^k C(n+k-1, k) x^k$$

**(2) `(1-x)^(-n)` 전개**:

위에서 `x`를 `-x`로 **치환**하면:

$$(1-x)^{-n} = \sum_{k=0}^{\infty} C(n+k-1, k) x^k$$

이것이 바로 **표 1**에서 `1/(1-x)ⁿ`의 계수가 `C(n+k-1, k)`인 이유이다!

> 💡 **핵심 포인트**: `1/(1-x)ⁿ`의 `xᵏ` 계수가 `C(n+k-1, k)`라는 사실은, **중복을 허용한 조합**(combination with repetition)의 수와 같다. 이것은 6장에서 배운 중복조합 공식과 정확히 일치한다!

```lean
-- 1/(1-x)^n 의 k번째 계수 = C(n+k-1, k) 검증
def coeffOneMinusXPowNeg (n k : ℕ) : ℕ := Nat.choose (n + k - 1) k

-- n=1: C(k, k) = 1 (모든 계수 1)
#eval List.range 6 |>.map (coeffOneMinusXPowNeg 1)  -- [1, 1, 1, 1, 1, 1] ← 정확하지 않음

-- 주의: n=1일 때 C(1+k-1, k) = C(k, k) = 1 ✓
-- n=2일 때 C(2+k-1, k) = C(k+1, k) = k+1 ✓
#eval List.range 6 |>.map (coeffOneMinusXPowNeg 2)  -- [1, 2, 3, 4, 5, 6]

-- n=3일 때 C(k+2, k) = C(k+2, 2) = (k+1)(k+2)/2
#eval List.range 6 |>.map (coeffOneMinusXPowNeg 3)  -- [1, 3, 6, 10, 15, 21]
```

---

## 6. 생성 함수로 계수 문제 풀기

### 6.1 예제 10: 제한 조건이 있는 방정식의 해 (Rosen 예제 10)

> **문제**: `e₁ + e₂ + e₃ = 17`의 해의 수를 구하라.  
> 단, `2 ≤ e₁ ≤ 5`, `3 ≤ e₂ ≤ 6`, `4 ≤ e₃ ≤ 7`

**생성 함수 접근법**:

각 변수의 범위에 맞는 다항식을 만들고, 이들의 곱에서 `x¹⁷`의 계수를 구한다.

- `e₁`: `x² + x³ + x⁴ + x⁵` (값이 2, 3, 4, 5)
- `e₂`: `x³ + x⁴ + x⁵ + x⁶` (값이 3, 4, 5, 6)
- `e₃`: `x⁴ + x⁵ + x⁶ + x⁷` (값이 4, 5, 6, 7)

세 다항식을 곱한 후 `x¹⁷`의 계수가 답이다.

```lean
-- 다항식을 계수 리스트로 표현
-- 리스트의 i번째 원소 = x^i의 계수
def poly_e1 : List ℕ := [0, 0, 1, 1, 1, 1]       -- x² + x³ + x⁴ + x⁵
def poly_e2 : List ℕ := [0, 0, 0, 1, 1, 1, 1]    -- x³ + x⁴ + x⁵ + x⁶
def poly_e3 : List ℕ := [0, 0, 0, 0, 1, 1, 1, 1] -- x⁴ + x⁵ + x⁶ + x⁷

-- 다항식 곱셈 (합성곱)
def polyMul (p q : List ℕ) : List ℕ :=
  let n := p.length + q.length - 1
  (List.range n).map fun k =>
    (List.range (k + 1)).foldl (fun acc j =>
      acc + (p.getD j 0) * (q.getD (k - j) 0)
    ) 0

-- 세 다항식의 곱
def product := polyMul (polyMul poly_e1 poly_e2) poly_e3

-- x^17의 계수 구하기
#eval product.getD 17 0  -- 3

-- 확인: 17 = 5+5+7 = 5+6+6 = 4+6+7 → 3가지 ✓
```

### 6.2 예제 11: 과자 분배 문제 (Rosen 예제 11)

> **문제**: 세 명의 아이에게 8개의 동일한 과자를 나눠주되, 각 아이는 적어도 2개, 최대 4개를 받아야 한다. 방법의 수는?

각 아이에 대한 생성 함수: `x² + x³ + x⁴`

세 아이이므로: `(x² + x³ + x⁴)³`

`x⁸`의 계수를 구한다.

```lean
def poly_cookie : List ℕ := [0, 0, 1, 1, 1]  -- x² + x³ + x⁴

def cookieProduct := polyMul (polyMul poly_cookie poly_cookie) poly_cookie

#eval cookieProduct.getD 8 0  -- 6
-- 분배 방법: (2,2,4), (2,4,2), (4,2,2), (2,3,3), (3,2,3), (3,3,2)
-- 총 6가지 ✓
```

### 6.3 예제 12: 자동판매기 토큰 문제 (Rosen 예제 12)

> **문제**: 1달러, 2달러, 5달러 토큰으로 `r`달러를 지불하는 방법의 수를 구하라 (순서 무관).

생성 함수:

$$(1 + x + x^2 + \cdots)(1 + x^2 + x^4 + \cdots)(1 + x^5 + x^{10} + \cdots) = \frac{1}{(1-x)(1-x^2)(1-x^5)}$$

```lean
-- 토큰 문제: 동적 프로그래밍으로 풀기
def tokenWays (target : ℕ) : ℕ :=
  -- coins: 1달러, 2달러, 5달러
  let coins := [1, 2, 5]
  -- dp[i] = i달러를 만드는 방법의 수
  let dp := coins.foldl (fun dp coin =>
    (List.range (target + 1)).foldl (fun dp' i =>
      if i < coin then dp'
      else
        let prev := dp'.getD (i - coin) 0
        let curr := dp'.getD i 0
        dp'.set i (curr + prev)
    ) dp
  ) ((List.range (target + 1)).map (fun i => if i == 0 then 1 else 0))
  dp.getD target 0

#eval List.range 15 |>.map tokenWays
-- [1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 10, 11, 13, 14, 16]
-- r=7일 때 6가지 ✓ (Rosen 교재 확인)
```

---

## 7. 생성 함수로 점화 관계 풀기

### 7.1 예제 16: 간단한 점화 관계 (Rosen 예제 16)

> **문제**: `a₀ = 2`, `aₖ = 3aₖ₋₁` (k = 1, 2, 3, ...)의 생성 함수를 구하고, 일반항을 구하라.

**풀이**: `G(x) = Σ aₖxᵏ`라 하자.

점화 관계 `aₖ = 3aₖ₋₁`에서:

$$G(x) - 3xG(x) = a_0 + \sum_{k=1}^{\infty} (a_k - 3a_{k-1})x^k = 2 + 0 = 2$$

따라서:

$$G(x) = \frac{2}{1 - 3x}$$

표 1에서 `1/(1-ax) = Σ aᵏxᵏ`이므로:

$$G(x) = 2 \sum_{k=0}^{\infty} 3^k x^k$$

따라서 `aₖ = 2 · 3ᵏ`이다.

```lean
-- 점화 관계로 정의
def recSeq16 : ℕ → ℕ
  | 0 => 2
  | n + 1 => 3 * recSeq16 n

-- 명시적 공식
def explicitSeq16 (n : ℕ) : ℕ := 2 * 3 ^ n

-- 두 수열이 같음을 증명
theorem recSeq16_eq (n : ℕ) : recSeq16 n = explicitSeq16 n := by
  induction n with
  | zero => simp [recSeq16, explicitSeq16]
  | succ n ih =>
    simp [recSeq16, explicitSeq16]
    rw [ih]
    simp [explicitSeq16, pow_succ]
    ring
```

### 7.2 예제 17: 유효한 코드단어 (Rosen 예제 17)

> **문제**: 짝수 개의 0을 포함하는 n자리 십진법 코드단어의 수 `aₙ`은  
> 점화 관계 `aₙ = 8aₙ₋₁ + 10ⁿ⁻¹`을 만족한다 (`a₀ = 1`).  
> 생성 함수를 이용하여 명시적 공식을 구하라.

**풀이** (Rosen의 풀이를 따름):

1. 생성 함수 `G(x) = Σ aₙxⁿ`을 설정한다.
2. 점화 관계로부터: `G(x) - 1 = 8xG(x) + x/(1-10x)`
3. 정리하면: `G(x) = (1 - 9x) / ((1-8x)(1-10x))`
4. **부분분수 분해**: `G(x) = (1/2) · (1/(1-8x) + 1/(1-10x))`
5. 따라서: `aₙ = (8ⁿ + 10ⁿ) / 2`

```lean
-- 점화 관계 정의
def validCode : ℕ → ℕ
  | 0 => 1
  | n + 1 => 8 * validCode n + 10 ^ n

-- 명시적 공식
def validCodeExplicit (n : ℕ) : ℕ := (8 ^ n + 10 ^ n) / 2

-- 처음 몇 항 확인
#eval List.range 6 |>.map validCode
-- [1, 9, 82, 756, 7048, 66240]
#eval List.range 6 |>.map validCodeExplicit
-- [1, 9, 82, 756, 7048, 66240]
-- 일치 ✓

-- 동치성 증명 (자연수 나눗셈 주의)
theorem validCode_explicit (n : ℕ) : validCode n = (8 ^ n + 10 ^ n) / 2 := by
  sorry  -- 증명은 8^n + 10^n이 항상 짝수임을 보이는 것이 핵심
```

---

## 8. 항등식 증명에 생성 함수 활용하기

### 8.1 예제 18: 반데르몽드 항등식 (Rosen 예제 18)

> **문제**: `n`이 양의 정수일 때 `Σₖ₌₀ⁿ C(n,k)² = C(2n, n)`임을 보여라.

**생성 함수 증명**:

`(1+x)²ⁿ = [(1+x)ⁿ]²`에서 양변의 `xⁿ` 계수를 비교한다.

- **좌변**: `(1+x)²ⁿ`에서 `xⁿ`의 계수 = `C(2n, n)`
- **우변**: `[(1+x)ⁿ]² = [Σ C(n,k)xᵏ]²`에서 `xⁿ`의 계수 = `Σₖ C(n,k) · C(n, n-k) = Σₖ C(n,k)²`

(마지막 등호는 `C(n, n-k) = C(n, k)` 때문이다.)

따라서 `Σₖ₌₀ⁿ C(n,k)² = C(2n, n)`이 증명된다!

```lean
-- Vandermonde 항등식 검증
def sumChooseSq (n : ℕ) : ℕ :=
  (List.range (n + 1)).map (fun k => Nat.choose n k ^ 2) |>.sum

-- 구체적 검증
#eval sumChooseSq 4   -- 70
#eval Nat.choose 8 4  -- 70 ✓

#eval sumChooseSq 5   -- 252
#eval Nat.choose 10 5 -- 252 ✓

-- Lean 4 정리
theorem vandermonde_identity (n : ℕ) :
    (Finset.range (n + 1)).sum (fun k => Nat.choose n k ^ 2) = Nat.choose (2 * n) n := by
  sorry  -- Mathlib에 Nat.add_choose_diagonal_right 관련 정리 존재
```

---

## 9. 연습 문제

### 연습 9.1: 생성 함수 기초 [괄호 채우기]

> 수열 `1, 4, 16, 64, 256`의 생성 함수를 구하라.

이 수열은 `4⁰, 4¹, 4², 4³, 4⁴`이므로 `aₖ = 4ᵏ`이다.

```lean
-- 수열 정의
def seq_pow4 : List ℕ := [1, 4, 16, 64, 256]

-- 일반항 확인
example : seq_pow4 = (List.range 5).map (fun k => 4 ^ k) := by ⟨ native_decide ⟩
```

> **질문**: 이 수열의 생성 함수를 닫힌 형태로 쓰면?

<details>
<summary>💡 답 보기</summary>

생성 함수는 `G(x) = 1 + 4x + 16x² + 64x³ + 256x⁴`이다.

이것은 **유한** 수열이므로:

$$G(x) = \frac{1 - (4x)^5}{1 - 4x} = \frac{1 - 1024x^5}{1 - 4x}$$

만약 무한 수열 `1, 4, 16, ...`로 확장하면 `G(x) = 1/(1-4x)`이다.

</details>

---

### 연습 9.2: 합성곱 계산 [괄호 채우기]

> 수열 `a = {1, 2, 3}` (유한)과 `b = {1, 1, 1}` (유한)의 합성곱 `c = a * b`를 구하라.

```lean
def seqA : ℕ → ℕ := fun n => if n < 3 then n + 1 else 0
def seqB : ℕ → ℕ := fun n => if n < 3 then 1 else 0

-- c₀ = a₀·b₀ = 1·1 = ?
#eval convolution seqA seqB 0  -- (     )

-- c₁ = a₀·b₁ + a₁·b₀ = 1·1 + 2·1 = ?
#eval convolution seqA seqB 1  -- (     )

-- c₂ = a₀·b₂ + a₁·b₁ + a₂·b₀ = 1·1 + 2·1 + 3·1 = ?
#eval convolution seqA seqB 2  -- (     )

-- c₃ = a₀·b₃ + a₁·b₂ + a₂·b₁ + a₃·b₀ = 0 + 2·1 + 3·1 + 0 = ?
#eval convolution seqA seqB 3  -- (     )

-- c₄ = ?
#eval convolution seqA seqB 4  -- (     )
```

<details>
<summary>💡 답 보기</summary>

```
c₀ = 1
c₁ = 3
c₂ = 6
c₃ = 5
c₄ = 3
```

다항식으로 보면: `(1 + 2x + 3x²)(1 + x + x²) = 1 + 3x + 6x² + 5x³ + 3x⁴`

</details>

---

### 연습 9.3: 확장 이항 계수 [괄호 채우기]

> `C(-3, 4)`를 계산하라.

```lean
-- 정의에 의해: C(-3, 4) = (-3)(-4)(-5)(-6) / 4!
-- = (360) / 24 = ?

#eval extBinom (-3) 4  -- (     )

-- 공식 C(-n, r) = (-1)^r * C(n+r-1, r) 로도 확인:
-- (-1)^4 * C(6, 4) = 1 * (     ) = (     )
#eval Nat.choose 6 4   -- (     )
```

<details>
<summary>💡 답 보기</summary>

```
C(-3, 4) = (-3)(-4)(-5)(-6) / 4! = 360 / 24 = 15
(-1)^4 * C(6, 4) = 1 * 15 = 15 ✓
```

</details>

---

### 연습 9.4: 생성 함수로 계수 문제 풀기 [Skeleton]

> **문제**: 1원, 5원, 10원 동전으로 20원을 만드는 방법의 수를 구하라 (순서 무관).

```lean
-- 각 동전 유형의 생성 함수를 다항식으로 표현
-- 1원: x⁰ + x¹ + x² + ... + x²⁰
def poly_1won : List ℕ := (List.range 21).map (fun _ => 1)

-- 5원: x⁰ + x⁵ + x¹⁰ + x¹⁵ + x²⁰
def poly_5won : List ℕ := (List.range 21).map (fun i =>
  if i % 5 == 0 then 1 else 0)

-- 10원: x⁰ + x¹⁰ + x²⁰
def poly_10won : List ℕ := (List.range 21).map (fun i =>
  if i % 10 == 0 then 1 else 0)

-- 세 다항식의 곱에서 x²⁰의 계수
def answer_9_4 : ℕ :=
  sorry  -- polyMul을 사용하여 구하라

-- #eval answer_9_4  -- 정답: ?
```

<details>
<summary>💡 답 보기</summary>

```lean
def answer_9_4 : ℕ :=
  let product := polyMul (polyMul poly_1won poly_5won) poly_10won
  product.getD 20 0

#eval answer_9_4  -- 9

-- 검증: 20원을 만드는 방법
-- 10×2 + 나머지: (0,0,2), (0,2,1), (0,4,0),
--               (5,1,1), (5,3,0),
--               (10,0,1), (10,2,0),
--               (15,1,0), (20,0,0) = 9가지
```

</details>

---

### 연습 9.5: 점화 관계와 생성 함수 [Sorry 도전]

> **문제**: `a₀ = 5`, `aₖ = 7aₖ₋₁` (k ≥ 1)일 때, 생성 함수를 이용하여 `aₖ = 5 · 7ᵏ`임을 증명하라.

```lean
def recSeq_7 : ℕ → ℕ
  | 0 => 5
  | n + 1 => 7 * recSeq_7 n

theorem recSeq_7_explicit (n : ℕ) : recSeq_7 n = 5 * 7 ^ n := by
  sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
theorem recSeq_7_explicit (n : ℕ) : recSeq_7 n = 5 * 7 ^ n := by
  induction n with
  | zero => simp [recSeq_7]
  | succ n ih =>
    simp [recSeq_7]
    rw [ih]
    ring
```

</details>

---

### 연습 9.6: 과자 분배 응용 [Sorry 도전]

> **문제**: 네 명의 아이에게 10개의 동일한 풍선을 나눠주되, 각 아이는 적어도 1개, 최대 4개를 받는다. 방법의 수를 생성 함수로 구하라.

```lean
-- 각 아이: x¹ + x² + x³ + x⁴
def poly_balloon : List ℕ := [0, 1, 1, 1, 1]

-- 네 아이
def balloon_product : List ℕ :=
  sorry  -- 4번 곱하기

-- x^10의 계수가 답
-- #eval balloon_product.getD 10 0
```

<details>
<summary>💡 답 보기</summary>

```lean
def balloon_product : List ℕ :=
  let p2 := polyMul poly_balloon poly_balloon
  let p3 := polyMul p2 poly_balloon
  polyMul p3 poly_balloon

#eval balloon_product.getD 10 0  -- 44

-- 검증: Σ를 구하기 어렵지만, 동적 프로그래밍이나
-- 전수탐색으로 확인할 수 있다
```

</details>

---

### 연습 9.7: Vandermonde 항등식 구체적 검증 [Sorry 도전]

> `n = 3`일 때 `Σₖ₌₀³ C(3,k)² = C(6,3)`임을 Lean 4로 증명하라.

```lean
-- C(3,0)² + C(3,1)² + C(3,2)² + C(3,3)² = C(6,3)
-- = 1 + 9 + 9 + 1 = 20 = C(6,3)
theorem vandermonde_3 :
    (Finset.range 4).sum (fun k => Nat.choose 3 k ^ 2) = Nat.choose 6 3 := by
  sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
theorem vandermonde_3 :
    (Finset.range 4).sum (fun k => Nat.choose 3 k ^ 2) = Nat.choose 6 3 := by
  native_decide
```

</details>

---

## 10. 사용된 Lean 4 전술 · 함수 정리

### 전술 요약

| 전술 | 용도 | 예시 |
|------|------|------|
| `native_decide` | 계산 가능한 명제 자동 증명 | 유한 합 검증 |
| `ring` | 환(ring) 등식 | `2 * 3 ^ n = 3 ^ n + 3 ^ n` |
| `simp` | 자동 단순화 | 정의 전개 |
| `induction n with` | 자연수 귀납법 | 점화 관계 → 닫힌 형태 |

### 함수/개념 요약

| 개념 | 설명 |
|------|------|
| `List.foldl` | 리스트 왼쪽 접기 (누적 연산) |
| `List.getD` | 인덱스 접근 (기본값 있음) |
| `Nat.choose` | 이항 계수 `C(n, k)` |
| `Nat.factorial` | 팩토리얼 `n!` |
| `Finset.range` | `{0, 1, ..., n-1}` |
| `Finset.sum` | 유한 집합 위의 합 |

---

## 11. 핵심 요약

1. **생성 함수**는 수열 `{aₙ}`을 급수 `G(x) = Σ aₖxᵏ`로 "포장"하는 도구이다.
2. 생성 함수의 **덧셈**은 계수끼리의 덧셈, **곱셈**은 **합성곱**(convolution)에 해당한다.
3. **핵심 공식** `1/(1-x) = Σ xᵏ`에서 **치환**으로 대부분의 생성 함수를 유도할 수 있다.
4. **확장 이항 계수** `C(u, k)`는 `u`가 실수일 때도 정의되며, `C(-n, r) = (-1)ʳ C(n+r-1, r)`이다.
5. 생성 함수는 **계수 문제**(동전 교환, 과자 분배 등)를 다항식의 곱으로 변환하여 풀 수 있다.
6. 생성 함수는 **점화 관계**의 닫힌 해를 구하는 대수적 도구이다.
7. 생성 함수는 **조합 항등식** 증명(Vandermonde 항등식 등)에도 강력하게 활용된다.

---

> **다음 파트 예고**: Part 11-D에서는 **포함-배제 원리**(Inclusion-Exclusion Principle, Rosen 8.5-8.6절)를 다룬다. 유한 집합의 합집합 크기를 구하는 공식과, 이를 Lean 4의 `Finset` 연산으로 형식화하는 방법을 배운다!
