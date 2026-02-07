# Lean 4 튜토리얼 — Part 9-E: 이항 정리와 파스칼 삼각형 (Binomial Theorem & Pascal's Triangle)

> **시리즈 위치**: Rosen 이산수학 8판 §6.4  
> **선수 지식**: Part 9-D (순열과 조합, Nat.choose)  
> **목표**: **이항 정리**(Binomial Theorem), **파스칼 항등식**(Pascal's Identity), 이항 계수의 다양한 항등식을 Lean 4로 이해하고 증명한다.

---

## 9E.0 이 장에서 배울 것

Part 9-D에서 배운 **조합의 수** C(n, r)은 사실 **이항 계수**(binomial coefficient)라고도 불린다. 왜 "이항"이라는 이름이 붙었을까? 그것은 (x + y)ⁿ을 전개할 때 각 항의 계수가 정확히 C(n, r)이기 때문이다! 이것이 유명한 **이항 정리**(Binomial Theorem)이다.

이 장에서는:
1. **이항 정리**: (x + y)ⁿ의 전개 공식
2. **파스칼 항등식**: C(n+1, k) = C(n, k-1) + C(n, k)
3. **파스칼 삼각형**: 이항 계수를 삼각형으로 배열
4. 이항 계수의 **합 공식**: ΣC(n, k) = 2ⁿ
5. **방데르몽드 항등식** 등 다양한 항등식

을 다룬다.

---

## 9E.1 **이항 정리**(Binomial Theorem)

### 9E.1.1 이항 표현이란?

**이항**(binomial)이란 x + y와 같은 **두 항의 합**(sum of two terms)을 의미한다. (x + y)ⁿ을 **이항 표현의 거듭 제곱식**(power of a binomial expression)이라 한다.

### 9E.1.2 작은 예부터 시작하자

(x + y)¹ = x + y — 이건 당연하다.

(x + y)² = x² + 2xy + y² — 이것도 중학교에서 배운다.

(x + y)³은? 교재 예제 1에서 조합 추론을 사용하여 구한다:

(x + y)³ = (x + y)(x + y)(x + y)를 전개할 때:
- **x³ 항**: 세 개의 괄호에서 모두 x를 선택 → 경우의 수 C(3, 0) = 1
- **x²y 항**: 세 개 중 두 개에서 x를, 한 개에서 y를 선택 → C(3, 1) = 3
- **xy² 항**: 세 개 중 한 개에서 x를, 두 개에서 y를 선택 → C(3, 2) = 3
- **y³ 항**: 세 개에서 모두 y를 선택 → C(3, 3) = 1

따라서: **(x + y)³ = x³ + 3x²y + 3xy² + y³**

계수가 1, 3, 3, 1인데, 이것이 바로 C(3, 0), C(3, 1), C(3, 2), C(3, 3)이다!

```lean
-- 이항 계수 확인
#eval Nat.choose 3 0  -- 1
#eval Nat.choose 3 1  -- 3
#eval Nat.choose 3 2  -- 3
#eval Nat.choose 3 3  -- 1
```

### 9E.1.3 이항 정리의 진술

> **정리 1** (이항 정리): x와 y를 변수라 하고 n을 음이 아닌 정수라 하자. 그러면  
> $$(x + y)^n = \sum_{j=0}^{n} \binom{n}{j} x^{n-j} y^j$$  
> $= \binom{n}{0}x^n + \binom{n}{1}x^{n-1}y + \cdots + \binom{n}{n-1}xy^{n-1} + \binom{n}{n}y^n$

말로 풀어쓰면: (x + y)ⁿ을 전개하면 각 항은 xⁿ⁻ʲyʲ의 형태이고, 그 계수는 C(n, j)이다.

**증명의 핵심 아이디어**: (x + y)ⁿ = (x + y)(x + y)···(x + y) (n번)을 전개할 때, xⁿ⁻ʲyʲ 항을 얻으려면 n개의 괄호 중에서 j개의 괄호에서 y를 선택하고 나머지 n-j개에서 x를 선택해야 한다. j개의 괄호를 선택하는 방법의 수가 C(n, j)이므로, xⁿ⁻ʲyʲ의 계수는 C(n, j)이 된다.

### 9E.1.4 교재 예제 2: (x + y)⁴의 전개

$$
(x + y)^4 = \binom{4}{0}x^4 + \binom{4}{1}x^3y + \binom{4}{2}x^2y^2 + \binom{4}{3}xy^3 + \binom{4}{4}y^4
$$
$$
= x^4 + 4x^3y + 6x^2y^2 + 4xy^3 + y^4
$$

```lean
-- 계수 확인
#eval Nat.choose 4 0  -- 1
#eval Nat.choose 4 1  -- 4
#eval Nat.choose 4 2  -- 6
#eval Nat.choose 4 3  -- 4
#eval Nat.choose 4 4  -- 1

-- 계수의 합: 1 + 4 + 6 + 4 + 1 = 16 = 2⁴
example : Nat.choose 4 0 + Nat.choose 4 1 + Nat.choose 4 2 +
          Nat.choose 4 3 + Nat.choose 4 4 = 16 := by native_decide
```

### 9E.1.5 교재 예제 3: (x + y)²⁵에서 x¹²y¹³의 계수

이항 정리에 의해 이 계수는 C(25, 13) = 5,200,300이다.

```lean
example : Nat.choose 25 13 = 5200300 := by native_decide
```

### 9E.1.6 교재 예제 4: (2x − 3y)²⁵에서 x¹²y¹³의 계수

(2x − 3y)²⁵ = (2x + (−3y))²⁵이므로 이항 정리에 의해:

x¹²y¹³의 계수는 j = 13일 때 얻어지므로:

$$\binom{25}{13} \cdot 2^{12} \cdot (-3)^{13}$$

이것은 **음수**가 된다 (−3을 홀수 번 곱하므로).

```lean
-- C(25, 13) = 5200300
example : Nat.choose 25 13 = 5200300 := by native_decide

-- 2^12 = 4096
example : 2^12 = 4096 := by norm_num

-- 3^13 = 1594323
example : (3 : ℕ)^13 = 1594323 := by norm_num
```

---

## 9E.2 이항 계수의 합 공식 (따름정리들)

### 9E.2.1 **따름정리 1**: 이항 계수의 합 = 2ⁿ

> **따름정리 1**: n이 음이 아닌 정수라면  
> $$\sum_{k=0}^{n} \binom{n}{k} = 2^n$$

**증명**: 이항 정리에서 x = 1, y = 1을 대입하면:

$$(1 + 1)^n = \sum_{k=0}^{n} \binom{n}{k} \cdot 1^{n-k} \cdot 1^k = \sum_{k=0}^{n} \binom{n}{k}$$

따라서 $\sum_{k=0}^{n} \binom{n}{k} = 2^n$이다.

**조합 증명**: 원소 수가 n개인 집합은 2ⁿ개의 서로 다른 부분집합을 갖는다. 이때 각 집합은 원소가 0개, 1개, 2개, ..., n개인 부분집합으로 나눌 수 있다. 원소가 k개인 부분집합은 C(n, k)개이다. 따라서 ΣC(n, k) = 2ⁿ이다.

```lean
import Mathlib

-- 구체적인 값으로 확인
-- n = 4: C(4,0) + C(4,1) + C(4,2) + C(4,3) + C(4,4) = 2^4 = 16
example : Nat.choose 4 0 + Nat.choose 4 1 + Nat.choose 4 2 +
          Nat.choose 4 3 + Nat.choose 4 4 = 2^4 := by native_decide

-- n = 5: 합 = 32
example : Nat.choose 5 0 + Nat.choose 5 1 + Nat.choose 5 2 +
          Nat.choose 5 3 + Nat.choose 5 4 + Nat.choose 5 5 = 2^5 := by native_decide

-- Mathlib에서는 Nat.sum_range_choose로 제공된다
-- Nat.sum_range_choose : ∀ (n : ℕ), ∑ i ∈ Finset.range (n + 1), n.choose i = 2 ^ n
```

### 9E.2.2 **따름정리 2**: 교대 합 = 0

> **따름정리 2**: n이 음이 아닌 정수라면  
> $$\sum_{k=0}^{n} (-1)^k \binom{n}{k} = 0$$

**증명**: 이항 정리에서 x = −1, y = 1을 대입하면:

$$((-1) + 1)^n = 0^n = 0 = \sum_{k=0}^{n} \binom{n}{k} (-1)^k$$

**의미**: 이것은 **짝수** 번째 이항 계수의 합과 **홀수** 번째 이항 계수의 합이 같다는 뜻이다!

$$\binom{n}{0} + \binom{n}{2} + \binom{n}{4} + \cdots = \binom{n}{1} + \binom{n}{3} + \binom{n}{5} + \cdots$$

```lean
-- n = 4에서 확인: 짝수 번째 합 = 홀수 번째 합
-- 짝수: C(4,0) + C(4,2) + C(4,4) = 1 + 6 + 1 = 8
-- 홀수: C(4,1) + C(4,3) = 4 + 4 = 8
example : Nat.choose 4 0 + Nat.choose 4 2 + Nat.choose 4 4 =
          Nat.choose 4 1 + Nat.choose 4 3 := by native_decide

-- n = 5에서도
example : Nat.choose 5 0 + Nat.choose 5 2 + Nat.choose 5 4 =
          Nat.choose 5 1 + Nat.choose 5 3 + Nat.choose 5 5 := by native_decide
```

### 9E.2.3 **따름정리 3**: 2ᵏ를 가중치로 한 합 = 3ⁿ

> **따름정리 3**: n이 음이 아닌 정수라면  
> $$\sum_{k=0}^{n} 2^k \binom{n}{k} = 3^n$$

**증명**: 이항 정리에서 x = 1, y = 2를 대입하면:

$$(1 + 2)^n = 3^n = \sum_{k=0}^{n} \binom{n}{k} 2^k$$

```lean
-- n = 3에서 확인
-- C(3,0)·1 + C(3,1)·2 + C(3,2)·4 + C(3,3)·8
-- = 1 + 6 + 12 + 8 = 27 = 3³
example : Nat.choose 3 0 * 1 + Nat.choose 3 1 * 2 +
          Nat.choose 3 2 * 4 + Nat.choose 3 3 * 8 = 3^3 := by native_decide

-- n = 4에서 확인
example : Nat.choose 4 0 * 1 + Nat.choose 4 1 * 2 + Nat.choose 4 2 * 4 +
          Nat.choose 4 3 * 8 + Nat.choose 4 4 * 16 = 3^4 := by native_decide
```

---

## 9E.3 **파스칼 항등식**(Pascal's Identity)과 **파스칼 삼각형**(Pascal's Triangle)

### 9E.3.1 파스칼 항등식

> **정리 2** (파스칼 항등식): n과 k가 n ≥ k인 양의 정수라 하면 다음이 성립한다.  
> $$\binom{n+1}{k} = \binom{n}{k-1} + \binom{n}{k}$$

말로 풀어쓰면: (n+1)개에서 k개를 선택하는 방법의 수는, n개에서 k-1개를 선택하는 방법의 수와 n개에서 k개를 선택하는 방법의 수의 합이다.

**왜 그런가?** (조합 증명)

T를 n+1개의 원소를 갖는 집합이라 하고, 특정 원소 a를 고정하자. T의 부분집합 중에서 k개의 원소를 갖는 것을 세는 두 가지 경우:

1. **a를 포함하는 경우**: a를 제외한 나머지 n개에서 k-1개를 더 선택 → C(n, k-1)
2. **a를 포함하지 않는 경우**: a를 제외한 나머지 n개에서 k개를 선택 → C(n, k)

합치면 C(n+1, k) = C(n, k-1) + C(n, k)이다.

### 9E.3.2 Lean 4에서의 파스칼 항등식

```lean
import Mathlib

-- 파스칼 항등식: C(n+1, k+1) = C(n, k) + C(n, k+1)
-- Mathlib에서는 Nat.choose_succ_succ로 제공된다
-- Nat.choose_succ_succ : n.choose (k+1) + n.choose k = (n+1).choose (k+1)

-- 구체적인 확인
-- C(5, 3) = C(4, 2) + C(4, 3)
example : Nat.choose 5 3 = Nat.choose 4 2 + Nat.choose 4 3 := by native_decide
-- 10 = 6 + 4 ✓

-- C(7, 4) = C(6, 3) + C(6, 4)
example : Nat.choose 7 4 = Nat.choose 6 3 + Nat.choose 6 4 := by native_decide
-- 35 = 20 + 15 ✓
```

### 9E.3.3 **파스칼 삼각형**(Pascal's Triangle)

파스칼 삼각형은 이항 계수를 삼각형 모양으로 배열한 것이다. 삼각형의 n번째 줄(0번째 줄부터 시작)은 C(n, 0), C(n, 1), ..., C(n, n)으로 구성된다.

```
n=0:                    1
n=1:                  1   1
n=2:                1   2   1
n=3:              1   3   3   1
n=4:            1   4   6   4   1
n=5:          1   5  10  10   5   1
n=6:        1   6  15  20  15   6   1
n=7:      1   7  21  35  35  21   7   1
n=8:    1   8  28  56  70  56  28   8   1
```

**파스칼 항등식의 의미**: 삼각형에서 인접한 두 개의 이항 계수를 더하면 다음 줄에 이항 계수가 나온다!

예: C(6, 4) + C(6, 5) = C(7, 5) → 15 + 6 = 21 ✓

이 삼각형은 프랑스 수학자 **블레즈 파스칼**(Blaise Pascal, 1623~1662)의 이름을 따서 **파스칼 삼각형**이라고 불린다. 다만, 동양에서는 이보다 훨씬 먼저 알려져 있었다. 기원전 2세기 인도 수학자 **핑갈라**(Pingala), 11세기 중국의 **가헌**(Jia Xian), 13세기 **양휘**(Yang Hui)에 의해 연구되었다.

```lean
-- 파스칼 삼각형의 8번째 줄 확인
#eval (List.range 9).map (Nat.choose 8)
-- [1, 8, 28, 56, 70, 56, 28, 8, 1]

-- 파스칼 삼각형 생성
#eval (List.range 8).map fun n =>
  (List.range (n + 1)).map (Nat.choose n)
-- [[1], [1,1], [1,2,1], [1,3,3,1], [1,4,6,4,1], ...]
```

---

## 9E.4 이항 계수의 다른 항등식

### 9E.4.1 **방데르몽드 항등식**(Vandermonde's Identity)

> **정리 3** (방데르몽드 항등식): m, n, r이 모두 음이 아닌 정수이고 r은 m 또는 n을 넘지 않는다고 하면, 다음이 성립한다.  
> $$\binom{m+n}{r} = \sum_{k=0}^{r} \binom{m}{r-k}\binom{n}{k}$$

**조합 증명**: 하나의 집합에 m개의 원소가 있고 또 다른 집합에 n개의 원소가 있다. 이 두 집합의 합집합에서 r개의 원소를 뽑는 방법은 C(m+n, r)이다.

한편, 첫 번째 집합에서 k개, 두 번째 집합에서 r-k개를 뽑는 방법은 C(m, r-k) × C(n, k)이다. k를 0부터 r까지 합하면 전체 방법의 수가 된다.

이 항등식은 18세기 수학자 **알렉상드로-테오필 방데르몽드**(Alexandre-Théophile Vandermonde)에 의해 발견되었다.

```lean
-- 방데르몽드 항등식의 구체적인 확인

-- m=3, n=4, r=3: C(7, 3) = ΣC(3, 3-k)C(4, k) for k=0..3
-- = C(3,3)C(4,0) + C(3,2)C(4,1) + C(3,1)C(4,2) + C(3,0)C(4,3)
-- = 1·1 + 3·4 + 3·6 + 1·4 = 1 + 12 + 18 + 4 = 35
example : Nat.choose 7 3 = 35 := by native_decide

example : Nat.choose 3 3 * Nat.choose 4 0 + Nat.choose 3 2 * Nat.choose 4 1 +
          Nat.choose 3 1 * Nat.choose 4 2 + Nat.choose 3 0 * Nat.choose 4 3 = 35 := by
  native_decide
```

### 9E.4.2 **따름정리 4**: 제곱합 공식

> **따름정리 4**: n이 음이 아닌 정수라면  
> $$\binom{2n}{n} = \sum_{k=0}^{n} \binom{n}{k}^2$$

**증명**: 방데르몽드 항등식에서 m = r = n을 대입하면 즉시 얻어진다.

```lean
-- n = 3: C(6, 3) = C(3,0)² + C(3,1)² + C(3,2)² + C(3,3)²
-- = 1 + 9 + 9 + 1 = 20
example : Nat.choose 6 3 = 20 := by native_decide
example : Nat.choose 3 0 ^ 2 + Nat.choose 3 1 ^ 2 +
          Nat.choose 3 2 ^ 2 + Nat.choose 3 3 ^ 2 = 20 := by native_decide

-- n = 4: C(8, 4) = 1 + 16 + 36 + 16 + 1 = 70
example : Nat.choose 8 4 = 70 := by native_decide
example : Nat.choose 4 0 ^ 2 + Nat.choose 4 1 ^ 2 + Nat.choose 4 2 ^ 2 +
          Nat.choose 4 3 ^ 2 + Nat.choose 4 4 ^ 2 = 70 := by native_decide
```

### 9E.4.3 **정리 4**: 하키 스틱 항등식

> **정리 4**: n과 r이 음이 아닌 정수이고 r ≤ n이라면  
> $$\binom{n+1}{r+1} = \sum_{j=r}^{n} \binom{j}{r}$$

이 항등식은 파스칼 삼각형에서 대각선 방향으로 더하면 다음 줄의 값이 나온다는 것을 표현한다. 그 모양이 **하키 스틱**(hockey stick)처럼 생겼다고 하여 붙은 이름이다.

```lean
-- 하키 스틱 항등식 확인
-- r=2, n=5: C(6, 3) = C(2,2) + C(3,2) + C(4,2) + C(5,2)
-- = 1 + 3 + 6 + 10 = 20
example : Nat.choose 6 3 = Nat.choose 2 2 + Nat.choose 3 2 +
          Nat.choose 4 2 + Nat.choose 5 2 := by native_decide

-- r=1, n=6: C(7, 2) = C(1,1) + C(2,1) + C(3,1) + C(4,1) + C(5,1) + C(6,1)
-- = 1 + 2 + 3 + 4 + 5 + 6 = 21
example : Nat.choose 7 2 = 1 + 2 + 3 + 4 + 5 + 6 := by native_decide
```

재미있지 않은가! C(7, 2) = 21 = 1 + 2 + 3 + 4 + 5 + 6이다. 즉 **삼각수**(triangular number)가 이항 계수와 연결된다!

---

## 9E.5 Lean 4에서 이항 정리 활용하기

### 9E.5.1 Mathlib의 이항 정리 관련 정리들

Lean 4의 Mathlib에는 이항 계수와 관련된 다양한 정리들이 이미 증명되어 있다:

```lean
import Mathlib

-- 파스칼 항등식
-- Nat.choose_succ_succ : ∀ (n k : ℕ), n.choose (k + 1) + n.choose k = (n + 1).choose (k + 1)
example (n k : ℕ) : Nat.choose n k + Nat.choose n (k + 1) = Nat.choose (n + 1) (k + 1) := by
  omega_nat
  -- 또는 Nat.choose_succ_succ를 직접 사용

-- 이항 계수의 합 = 2^n
-- Nat.sum_range_choose : ∀ (n : ℕ), ∑ i ∈ Finset.range (n + 1), n.choose i = 2 ^ n

-- choose의 기본 성질들
example (n : ℕ) : Nat.choose n 0 = 1 := Nat.choose_zero_right n
example (n : ℕ) : Nat.choose n n = 1 := Nat.choose_self n
example (n : ℕ) : Nat.choose n 1 = n := Nat.choose_one_right n
```

### 9E.5.2 `Nat.choose_succ_succ` 정리의 활용

파스칼 항등식은 Lean에서 이항 계수를 재귀적으로 계산하는 핵심이다:

```lean
-- 파스칼 항등식을 이용한 계산
-- C(5, 2) = C(4, 1) + C(4, 2) = 4 + 6 = 10
example : Nat.choose 5 2 = Nat.choose 4 1 + Nat.choose 4 2 := by
  -- Nat.choose_succ_succ를 사용
  native_decide

-- 한 단계 더: C(4, 2) = C(3, 1) + C(3, 2) = 3 + 3 = 6
example : Nat.choose 4 2 = Nat.choose 3 1 + Nat.choose 3 2 := by native_decide
```

---

## 9E.6 종합 연습문제

### 🏋️ 연습 9E-1: (x + y)⁶의 이항 계수 (괄호 채우기)

```lean
-- (x + y)⁶의 전개에서 각 항의 계수를 구하라
-- 계수는 C(6, 0), C(6, 1), ..., C(6, 6)이다

example : Nat.choose 6 0 = ⟨___⟩ := by native_decide
example : Nat.choose 6 1 = ⟨___⟩ := by native_decide
example : Nat.choose 6 2 = ⟨___⟩ := by native_decide
example : Nat.choose 6 3 = ⟨___⟩ := by native_decide
-- (나머지는 대칭이다: C(6,4) = C(6,2), C(6,5) = C(6,1), C(6,6) = C(6,0))
```

<details>
<summary>🔑 답 보기</summary>

```lean
example : Nat.choose 6 0 = 1 := by native_decide
example : Nat.choose 6 1 = 6 := by native_decide
example : Nat.choose 6 2 = 15 := by native_decide
example : Nat.choose 6 3 = 20 := by native_decide
```

**해설**: (x + y)⁶ = x⁶ + 6x⁵y + 15x⁴y² + 20x³y³ + 15x²y⁴ + 6xy⁵ + y⁶이다. 계수를 나열하면 1, 6, 15, 20, 15, 6, 1로 파스칼 삼각형의 6번째 줄이다.

</details>

### 🏋️ 연습 9E-2: (x + y)¹³에서 x⁵y⁸의 계수 (교재 연습문제 4 기반)

```lean
-- (x + y)¹³의 전개에서 x⁵y⁸의 계수는?
-- j = 8이므로 C(13, 8) = ?
example : Nat.choose 13 8 = ⟨___⟩ := by native_decide
```

<details>
<summary>🔑 답 보기</summary>

```lean
example : Nat.choose 13 8 = 1287 := by native_decide
```

**해설**: 이항 정리에서 x^(13-j) · y^j이므로, j = 8일 때 x⁵y⁸이 나온다. 계수는 C(13, 8) = C(13, 5) = 1287이다.

</details>

### 🏋️ 연습 9E-3: 파스칼 항등식 확인 (괄호 채우기)

```lean
-- 파스칼 항등식: C(n+1, k) = C(n, k-1) + C(n, k)
-- 다음을 확인하라

-- C(8, 3) = C(7, 2) + C(7, 3) = ? + ? = ?
example : Nat.choose 8 3 = Nat.choose 7 2 + Nat.choose 7 3 := by ⟨___⟩

-- C(10, 5) = C(9, 4) + C(9, 5) = ? + ? = ?
example : Nat.choose 10 5 = Nat.choose 9 4 + Nat.choose 9 5 := by ⟨___⟩
```

<details>
<summary>🔑 답 보기</summary>

```lean
-- C(8, 3) = 21 + 35 = 56
example : Nat.choose 8 3 = Nat.choose 7 2 + Nat.choose 7 3 := by native_decide

-- C(10, 5) = 126 + 126 = 252
example : Nat.choose 10 5 = Nat.choose 9 4 + Nat.choose 9 5 := by native_decide
```

</details>

### 🏋️ 연습 9E-4: 이항 계수의 합 = 2ⁿ 확인 (괄호 채우기)

```lean
-- ΣC(n, k) = 2^n을 확인하라

-- n = 6: C(6,0) + C(6,1) + ... + C(6,6) = ?
example : Nat.choose 6 0 + Nat.choose 6 1 + Nat.choose 6 2 + Nat.choose 6 3 +
          Nat.choose 6 4 + Nat.choose 6 5 + Nat.choose 6 6 = ⟨___⟩ := by native_decide

-- n = 7: 합 = ?
example : Nat.choose 7 0 + Nat.choose 7 1 + Nat.choose 7 2 + Nat.choose 7 3 +
          Nat.choose 7 4 + Nat.choose 7 5 + Nat.choose 7 6 + Nat.choose 7 7 = ⟨___⟩ := by
  native_decide
```

<details>
<summary>🔑 답 보기</summary>

```lean
-- n = 6: 합 = 64 = 2^6
example : Nat.choose 6 0 + Nat.choose 6 1 + Nat.choose 6 2 + Nat.choose 6 3 +
          Nat.choose 6 4 + Nat.choose 6 5 + Nat.choose 6 6 = 64 := by native_decide

-- n = 7: 합 = 128 = 2^7
example : Nat.choose 7 0 + Nat.choose 7 1 + Nat.choose 7 2 + Nat.choose 7 3 +
          Nat.choose 7 4 + Nat.choose 7 5 + Nat.choose 7 6 + Nat.choose 7 7 = 128 := by
  native_decide
```

</details>

### 🏋️ 연습 9E-5: 짝수/홀수 번째 이항 계수의 합이 같음 (sorry 방식)

```lean
-- 따름정리 2의 결과: 짝수 번째 합 = 홀수 번째 합
-- n = 6에서 확인하라
example : Nat.choose 6 0 + Nat.choose 6 2 + Nat.choose 6 4 + Nat.choose 6 6 =
          Nat.choose 6 1 + Nat.choose 6 3 + Nat.choose 6 5 := by sorry
```

<details>
<summary>🔑 답 보기</summary>

```lean
example : Nat.choose 6 0 + Nat.choose 6 2 + Nat.choose 6 4 + Nat.choose 6 6 =
          Nat.choose 6 1 + Nat.choose 6 3 + Nat.choose 6 5 := by native_decide
-- 1 + 15 + 15 + 1 = 32 = 6 + 20 + 6 ✓
```

</details>

### 🏋️ 연습 9E-6: 방데르몽드 항등식 확인 (sorry 방식)

```lean
-- 방데르몽드 항등식 C(m+n, r) = Σ C(m, r-k)C(n, k)
-- m=4, n=3, r=3에서 확인하라
-- C(7, 3) = C(4,3)C(3,0) + C(4,2)C(3,1) + C(4,1)C(3,2) + C(4,0)C(3,3)
example : Nat.choose 7 3 = Nat.choose 4 3 * Nat.choose 3 0 +
          Nat.choose 4 2 * Nat.choose 3 1 + Nat.choose 4 1 * Nat.choose 3 2 +
          Nat.choose 4 0 * Nat.choose 3 3 := by sorry
```

<details>
<summary>🔑 답 보기</summary>

```lean
example : Nat.choose 7 3 = Nat.choose 4 3 * Nat.choose 3 0 +
          Nat.choose 4 2 * Nat.choose 3 1 + Nat.choose 4 1 * Nat.choose 3 2 +
          Nat.choose 4 0 * Nat.choose 3 3 := by native_decide
-- 35 = 4·1 + 6·3 + 4·3 + 1·1 = 4 + 18 + 12 + 1 = 35 ✓
```

</details>

### 🏋️ 연습 9E-7: 하키 스틱 항등식 확인 (sorry 방식)

```lean
-- 하키 스틱 항등식: C(n+1, r+1) = Σ_{j=r}^{n} C(j, r)
-- r=3, n=6: C(7, 4) = C(3,3) + C(4,3) + C(5,3) + C(6,3)
example : Nat.choose 7 4 = Nat.choose 3 3 + Nat.choose 4 3 +
          Nat.choose 5 3 + Nat.choose 6 3 := by sorry
```

<details>
<summary>🔑 답 보기</summary>

```lean
example : Nat.choose 7 4 = Nat.choose 3 3 + Nat.choose 4 3 +
          Nat.choose 5 3 + Nat.choose 6 3 := by native_decide
-- 35 = 1 + 4 + 10 + 20 = 35 ✓
```

</details>

### 🏋️ 연습 9E-8: 따름정리 4 확인 (sorry 방식)

```lean
-- 따름정리 4: C(2n, n) = Σ C(n, k)²
-- n = 5: C(10, 5) = C(5,0)² + C(5,1)² + C(5,2)² + C(5,3)² + C(5,4)² + C(5,5)²
example : Nat.choose 10 5 = Nat.choose 5 0 ^ 2 + Nat.choose 5 1 ^ 2 +
          Nat.choose 5 2 ^ 2 + Nat.choose 5 3 ^ 2 + Nat.choose 5 4 ^ 2 +
          Nat.choose 5 5 ^ 2 := by sorry
```

<details>
<summary>🔑 답 보기</summary>

```lean
example : Nat.choose 10 5 = Nat.choose 5 0 ^ 2 + Nat.choose 5 1 ^ 2 +
          Nat.choose 5 2 ^ 2 + Nat.choose 5 3 ^ 2 + Nat.choose 5 4 ^ 2 +
          Nat.choose 5 5 ^ 2 := by native_decide
-- 252 = 1 + 25 + 100 + 100 + 25 + 1 = 252 ✓
```

</details>

### 🏋️ 연습 9E-9: 파스칼 삼각형 9번째 줄 (교재 연습문제 17 기반)

```lean
-- 파스칼 삼각형에서 k가 0 ≤ k ≤ 9일 때 이항 계수 C(9, k)를 포함하는 줄을 완성하라
-- C(9, 0) = 1, C(9, 1) = ?, C(9, 2) = ?, C(9, 3) = ?, C(9, 4) = ?
-- (대칭이므로 나머지는 같다)

example : Nat.choose 9 1 = ⟨___⟩ := by native_decide
example : Nat.choose 9 2 = ⟨___⟩ := by native_decide
example : Nat.choose 9 3 = ⟨___⟩ := by native_decide
example : Nat.choose 9 4 = ⟨___⟩ := by native_decide
```

<details>
<summary>🔑 답 보기</summary>

```lean
example : Nat.choose 9 1 = 9 := by native_decide
example : Nat.choose 9 2 = 36 := by native_decide
example : Nat.choose 9 3 = 84 := by native_decide
example : Nat.choose 9 4 = 126 := by native_decide
```

**해설**: 파스칼 삼각형의 9번째 줄은: 1, 9, 36, 84, 126, 126, 84, 36, 9, 1이다.

</details>

### 🏋️ 연습 9E-10: 종합 문제 — (x + y)¹⁰⁰의 항의 수 (교재 연습문제 5 기반)

```lean
-- (x + y)¹⁰⁰의 전개식에는 몇 개의 항이 있는가?
-- 이항 정리에 의해 j = 0, 1, 2, ..., 100이므로 101개의 항이 있다.
-- (어떤 항도 0이 되지 않는다고 가정)
example : 100 + 1 = ⟨___⟩ := by norm_num
```

<details>
<summary>🔑 답 보기</summary>

```lean
example : 100 + 1 = 101 := by norm_num
```

**해설**: (x + y)ⁿ의 전개식은 n+1개의 항을 갖는다 (j = 0부터 n까지).

</details>

### 🏋️ 연습 9E-11: (1 + x)¹¹에서 x⁷의 계수 (교재 연습문제 6 기반)

```lean
-- (1 + x)¹¹에서 x⁷의 계수는?
-- 이항 정리에서 y = x, x = 1로 놓으면
-- C(11, 7) = ?
example : Nat.choose 11 7 = ⟨___⟩ := by native_decide
```

<details>
<summary>🔑 답 보기</summary>

```lean
example : Nat.choose 11 7 = 330 := by native_decide
```

**해설**: (1 + x)¹¹ = Σ C(11, j) · x^j이므로, x⁷의 계수는 C(11, 7) = C(11, 4) = 330이다.

</details>

### 🏋️ 연습 9E-12: (2 − x)¹⁹에서 x⁹의 계수 (교재 연습문제 7 기반)

```lean
-- (2 − x)¹⁹ = (2 + (−x))¹⁹
-- x⁹의 계수: C(19, 9) × 2^10 × (-1)^9
-- 절대값: C(19, 9) × 2^10

-- C(19, 9) = ?
example : Nat.choose 19 9 = ⟨___⟩ := by native_decide

-- 2^10 = ?
example : (2 : ℕ)^10 = ⟨___⟩ := by norm_num
```

<details>
<summary>🔑 답 보기</summary>

```lean
-- C(19, 9) = 92378
example : Nat.choose 19 9 = 92378 := by native_decide

-- 2^10 = 1024
example : (2 : ℕ)^10 = 1024 := by norm_num

-- 절대값: 92378 * 1024 = 94595072
-- 부호: (-1)^9 = -1이므로 실제 계수는 -94595072
```

</details>

---

## 9E.7 이 장의 핵심 요약

| 항등식 | 공식 | Lean 4 관련 도구 |
|------|------|---------------|
| **이항 정리** | $(x+y)^n = \sum C(n,j) x^{n-j} y^j$ | `Commute.add_pow` |
| **따름정리 1** | $\sum C(n,k) = 2^n$ | `Nat.sum_range_choose` |
| **따름정리 2** | 짝수 합 = 홀수 합 | `native_decide` |
| **따름정리 3** | $\sum 2^k C(n,k) = 3^n$ | `native_decide` |
| **파스칼 항등식** | $C(n+1,k) = C(n,k-1) + C(n,k)$ | `Nat.choose_succ_succ` |
| **대칭성** | $C(n,r) = C(n,n-r)$ | `Nat.choose_symm` |
| **방데르몽드** | $C(m+n,r) = \sum C(m,r-k)C(n,k)$ | `Nat.add_choose_eq` |
| **하키 스틱** | $C(n+1,r+1) = \sum_{j=r}^{n} C(j,r)$ | `native_decide` |

### 주요 Lean 4 함수 및 전술 (추가)

| 함수/전술 | 용도 |
|---------|------|
| `Nat.choose_succ_succ` | 파스칼 항등식 |
| `Nat.choose_one_right` | C(n, 1) = n |
| `Nat.sum_range_choose` | ΣC(n, k) = 2ⁿ |

---

> **다음 편 예고**: Part 9-F에서는 **일반화된 순열과 조합**(Generalized Permutations and Combinations)을 다룬다. 반복을 허용하는 순열, 구별할 수 없는 원소가 있는 경우, 그리고 중복 조합 등 더 풍부한 계수 문제를 Lean 4로 탐구한다.
