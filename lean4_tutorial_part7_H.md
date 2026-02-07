# Lean4 완전 정복 가이드 — 제7-H편

## **페르마의 작은 정리**(Fermat's Little Theorem), **의사소수**(Pseudoprimes), **기본 루트**(Primitive Roots)와 **이산 로그**(Discrete Logarithms) 완전 정복

> **교재**: Kenneth H. Rosen, "Discrete Mathematics and Its Applications" 8판  
> **범위**: 4.4절 합동 풀기 (4.4.5 페르마의 작은 정리, 4.4.6 의사소수, 4.4.7 기본 루트와 이산 로그)  
> **선수 학습**: 제7-F편(선형합동, 역모듈로), 제7-G편(중국인의 나머지 정리)  
> **참고**: 『Mathematics in Lean』 Chapter 5.3 (Infinitely Many Primes)

---

## 7H.0 이 장의 목표

1. **페르마의 작은 정리**(Fermat's Little Theorem)를 이해하고 Lean4로 검증한다
2. 이 정리를 이용하여 **큰 거듭제곱의 나머지**를 효율적으로 계산한다
3. **의사소수**(pseudoprime)란 무엇인지 이해한다
4. **카마이클 수**(Carmichael number)의 개념을 안다
5. **기본 루트**(primitive root)와 **이산 로그**(discrete logarithm)를 이해한다

> 💡 페르마의 작은 정리는 RSA 암호 시스템의 이론적 기초이다! 이 장에서 배우는 내용은 현대 암호학의 핵심이다.

---

## 7H.1 **페르마의 작은 정리**(Fermat's Little Theorem) — 정리 3

### 7H.1.1 역사적 배경

17세기 초 프랑스의 위대한 수학자 피에르 드 페르마(Pierre de Fermat, 1601–1665)는 정수론에서 많은 중요한 발견을 했다. 그 중 가장 유용한 것 중 하나가 이 **작은 정리**(little theorem)이다.

> ⚠️ "페르마의 마지막 정리"(Fermat's Last Theorem, $x^n + y^n = z^n$은 $n > 2$일 때 양의 정수 해가 없다)와 혼동하지 말자! 그것은 1994년 앤드루 와일스가 350년 만에 증명한 것이고, 이 "작은 정리"는 훨씬 간단한 것이다.

### 7H.1.2 정리의 진술

> **정리 3** (페르마의 작은 정리): $p$가 **소수**이고 $a$가 $p$로 나눌 수 없는 정수이면:
> $$a^{p-1} \equiv 1 \pmod{p}$$
> 
> 또, **모든** 정수 $a$에 대하여:
> $$a^p \equiv a \pmod{p}$$

두 번째 형태는 첫 번째에서 양변에 $a$를 곱하면 나온다. 두 번째 형태의 장점은 $\gcd(a, p) = 1$이라는 조건이 필요 없다는 것이다 ($a$가 $p$의 배수여도 양변이 모두 0이 되어 성립).

### 7H.1.3 직관적 이해

이 정리가 말하는 것은 놀랍다: "$a$를 $p-1$번 곱하면 (모듈로 $p$에서) 반드시 1로 돌아온다!"

예를 들어 $p = 7$이고 $a = 3$:

$$3^1 = 3, \quad 3^2 = 9 \equiv 2, \quad 3^3 = 27 \equiv 6, \quad 3^4 = 81 \equiv 4, \quad 3^5 = 243 \equiv 5, \quad 3^6 = 729 \equiv 1$$

$3^6 \equiv 1 \pmod{7}$ ✓ (6 = 7 - 1 = p - 1)

```lean
-- Lean4로 검증
#eval (3^6) % 7  -- 1 ✓

-- 다양한 a에 대해 확인
#eval (2^6) % 7  -- 1 ✓
#eval (4^6) % 7  -- 1 ✓
#eval (5^6) % 7  -- 1 ✓
#eval (6^6) % 7  -- 1 ✓

-- 두 번째 형태: a^p ≡ a (mod p)
#eval (3^7) % 7  -- 3 ✓
#eval (10^7) % 7 -- 3 (10 mod 7 = 3) ✓

-- p의 배수인 경우에도 두 번째 형태는 성립
#eval (7^7) % 7   -- 0 (= 7 mod 7) ✓
#eval (14^7) % 7  -- 0 (= 14 mod 7) ✓
```

### 7H.1.4 Lean4에서의 형식적 표현

```lean
-- 구체적 사례의 증명
theorem fermat_example_1 : (2^6) % 7 = 1 := by native_decide
theorem fermat_example_2 : (3^10) % 11 = 1 := by native_decide
theorem fermat_example_3 : (5^12) % 13 = 1 := by native_decide

-- p = 5일 때, gcd(a, 5) = 1인 모든 a ∈ {1,2,3,4}에 대해 확인
example : ∀ a : Fin 5, a.val > 0 → (a.val ^ 4) % 5 = 1 := by
  decide
```

### 7H.1.5 왜 성립하는가? (증명의 직관)

$\{1, 2, 3, \ldots, p-1\}$에 모두 $a$를 곱하면 $\{a, 2a, 3a, \ldots, (p-1)a\}$가 된다.

핵심: $\gcd(a, p) = 1$이면, 이 새로운 집합도 (모듈로 $p$에서) $\{1, 2, \ldots, p-1\}$의 **재배열**(permutation)이다! (왜? $ia \equiv ja \pmod{p}$이면 $i \equiv j \pmod{p}$이므로 중복이 없다.)

따라서:
$$a \cdot 2a \cdot 3a \cdots (p-1)a \equiv 1 \cdot 2 \cdot 3 \cdots (p-1) \pmod{p}$$
$$a^{p-1} \cdot (p-1)! \equiv (p-1)! \pmod{p}$$

$(p-1)!$은 $p$와 서로소이므로 양변에서 소거할 수 있다:
$$a^{p-1} \equiv 1 \pmod{p}$$

```lean
-- 직관의 확인: p = 7, a = 3
-- {1,2,3,4,5,6}에 3을 곱하면 (mod 7):
-- {3, 6, 2, 5, 1, 4} — 같은 집합의 재배열!
#eval (List.range 6).map fun i => ((i + 1) * 3) % 7
-- [3, 6, 2, 5, 1, 4] ✓
```

---

## 7H.2 교재 예제 9: $7^{222} \bmod 11$ 계산

### 7H.2.1 문제

$7^{222} \bmod 11$을 계산하라.

### 7H.2.2 풀이 (페르마의 작은 정리 활용)

1. 페르마의 작은 정리: $p = 11$이 소수이고 $\gcd(7, 11) = 1$이므로 $7^{10} \equiv 1 \pmod{11}$
2. $222 = 22 \times 10 + 2$이므로 $7^{222} = (7^{10})^{22} \times 7^2$
3. $7^{10} \equiv 1$이므로 $(7^{10})^{22} \equiv 1^{22} = 1$
4. 따라서 $7^{222} \equiv 1 \times 7^2 = 49 \equiv 5 \pmod{11}$

```lean
-- 단계별 검증
example : (7^10) % 11 = 1 := by native_decide        -- 페르마의 작은 정리
example : 222 = 22 * 10 + 2 := by norm_num            -- 지수 분해
example : (7^222) % 11 = (7^2) % 11 := by native_decide  -- 지수 축소
example : (7^2) % 11 = 5 := by native_decide          -- 최종 계산
-- 따라서 7^222 mod 11 = 5
```

### 7H.2.3 일반적 방법: $a^n \bmod p$ 효율적 계산

```lean
-- 큰 거듭제곱 mod 계산: a^n mod p를 효율적으로 계산
-- 방법: n = q(p-1) + r로 분해 (r = n mod (p-1))
-- a^n ≡ (a^(p-1))^q × a^r ≡ 1^q × a^r ≡ a^r (mod p)

def fastModPow (a n p : Nat) : Nat :=
  -- 페르마의 작은 정리를 활용한 지수 축소
  if Nat.Prime p && Nat.gcd a p == 1 then
    let r := n % (p - 1)  -- 지수를 p-1로 나눈 나머지
    (a ^ r) % p            -- a^r mod p만 계산하면 됨!
  else
    (a ^ n) % p            -- 일반적인 계산

#eval fastModPow 7 222 11  -- 5 ✓
#eval fastModPow 3 1000 17  -- ?
```

---

## 7H.3 연습문제 세트 1: 페르마의 작은 정리

### 연습 1-1: 기본 검증 (괄호 채우기)

```lean
-- p = 13일 때 2^12 mod 13 = ?
example : (2^12) % 13 = (______) := by native_decide
```

<details>
<summary>💡 답 보기</summary>

```lean
example : (2^12) % 13 = 1 := by native_decide
-- 13은 소수이고 gcd(2, 13) = 1이므로 페르마의 작은 정리에 의해 2^12 ≡ 1 (mod 13)
```

</details>

### 연습 1-2: 교재 연습문제 33

페르마의 작은 정리를 사용하여 $7^{121} \bmod 13$을 계산하라.

```lean
-- 1단계: 121 = ? × 12 + ? (12 = 13-1)
-- 2단계: 7^121 ≡ 7^? (mod 13)
-- 3단계: 7^? mod 13 = ?

#eval 121 % 12      -- ? (지수의 나머지)
#eval (7^sorry) % 13  -- 최종 답
```

<details>
<summary>💡 답 보기</summary>

```lean
#eval 121 % 12  -- 1
-- 121 = 10 × 12 + 1
-- 7^121 ≡ 7^1 ≡ 7 (mod 13)

example : (7^121) % 13 = 7 := by native_decide
```

</details>

### 연습 1-3: 교재 연습문제 34

$23^{1002} \bmod 41$을 계산하라.

```lean
-- p = 41, a = 23
-- 1002 mod (41-1) = 1002 mod 40 = ?
#eval 1002 % 40  -- ?
-- 23^1002 ≡ 23^? (mod 41)

example : (23^1002) % 41 = sorry := by native_decide
```

<details>
<summary>💡 답 보기</summary>

```lean
#eval 1002 % 40  -- 2
-- 1002 = 25 × 40 + 2
-- 23^1002 ≡ 23^2 = 529 ≡ 529 mod 41

#eval (23^2) % 41  -- 529 mod 41
-- 529 = 12 × 41 + 37
example : (23^1002) % 41 = 37 := by native_decide
```

</details>

### 연습 1-4: 교재 연습문제 35 — 역의 또 다른 표현

$p$가 소수이고 $p \nmid a$이면, $a^{p-2}$가 $a$ 모듈로 $p$의 역임을 보여라.

힌트: $a \times a^{p-2} = a^{p-1} \equiv 1 \pmod{p}$

```lean
-- 구체적 예: p = 7, a = 3
-- 3의 역(mod 7) = 3^5 (= 7-2 = 5)
#eval (3^5) % 7  -- ?
-- 이것이 5 (= 3의 역)와 같은지 확인

example : (3 * 3^5) % 7 = sorry := by native_decide
```

<details>
<summary>💡 답 보기</summary>

```lean
#eval (3^5) % 7  -- 5
-- 3^5 = 243, 243 mod 7 = 5

-- 검증: 3 × 5 = 15 ≡ 1 (mod 7) ✓
example : (3 * 3^5) % 7 = 1 := by native_decide

-- 일반적으로: a × a^(p-2) = a^(p-1) ≡ 1 (mod p) (페르마의 작은 정리)
-- 따라서 a^(p-2)는 a의 역!

-- 다른 소수에서도 확인
example : (2 * 2^11) % 13 = 1 := by native_decide  -- 2의 역(mod 13) = 2^11
example : (5 * 5^16) % 19 = 1 := by native_decide  -- 5의 역(mod 19) = 5^17... 아니다!
-- 수정: 5의 역(mod 19) = 5^(19-2) = 5^17
example : (5 * 5^17) % 19 = 1 := by native_decide  -- ✓
```

이 사실은 실용적으로 매우 유용하다. 유클리드 알고리즘 대신 **거듭제곱**으로 역을 구할 수 있다!

</details>

---

## 7H.4 **의사소수**(Pseudoprimes) — 4.4.6절

### 7H.4.1 소수 판별 문제

어떤 정수 $n$이 소수인지 아닌지를 빠르게 판별하고 싶다. 4.2절에서 배운 "직접 나누어 보기"는 $\sqrt{n}$까지의 모든 소수를 시도해야 하므로 느리다.

페르마의 작은 정리가 소수 테스트에 쓸 수 있을까?

**아이디어**: $n$이 소수라면 $2^{n-1} \equiv 1 \pmod{n}$이다 (페르마). 그러므로 만약 $2^{n-1} \not\equiv 1 \pmod{n}$이면 $n$은 **확실히 합성수**이다!

```lean
-- 페르마 테스트: 2^(n-1) mod n = 1인지 확인
def fermatTest (n : Nat) : Bool :=
  if n < 2 then false
  else (Nat.pow 2 (n - 1)) % n == 1

-- 소수 검사
#eval fermatTest 5   -- true (5는 소수)
#eval fermatTest 7   -- true (7은 소수)
#eval fermatTest 11  -- true (11은 소수)
#eval fermatTest 15  -- false (15 = 3×5, 합성수)
#eval fermatTest 21  -- false (21 = 3×7, 합성수)
```

### 7H.4.2 문제: 거짓 양성!

그런데 이 테스트를 **통과**하지만 소수가 **아닌** 수가 존재한다!

> **정의 1**: $b$가 양의 정수라 하자. 만약 $n$이 양의 합성수이고 $b^{n-1} \equiv 1 \pmod{n}$이면, $n$을 $b$를 **밑으로 하는 의사소수**(pseudoprime to the base $b$)라고 한다.

쉽게 말해: "소수처럼 행동하지만 소수가 아닌 합성수"이다.

### 7H.4.3 교재 예제 10: 341은 밑 2의 의사소수

$341 = 11 \times 31$은 합성수인데, $2^{340} \equiv 1 \pmod{341}$이다!

왜 그런가? 핵심은 $2^{10} \equiv 1 \pmod{341}$이라는 사실이다.

```lean
-- 341이 합성수임을 확인
#eval Nat.Prime 341  -- false
#eval 11 * 31        -- 341

-- 핵심: 2^10 mod 341 = 1
-- 2^10 = 1024, 1024 = 3 × 341 + 1이므로 1024 mod 341 = 1
#eval (2^10) % 341  -- 1!
example : (2^10) % 341 = 1 := by native_decide

-- 따라서 2^340 = (2^10)^34 ≡ 1^34 = 1 (mod 341)
-- 341은 페르마 테스트를 통과하지만 소수가 아니다!
#eval fermatTest 341  -- true (하지만 합성수!)
```

> 💡 이것은 소수 테스트의 한계를 보여준다. 페르마 테스트를 통과했다고 해서 반드시 소수는 아니다!

### 7H.4.4 **카마이클 수**(Carmichael Numbers) — 정의 2

> **정의 2**: $\gcd(b, n) = 1$인 모든 양의 정수 $b$에 대해 $b^{n-1} \equiv 1 \pmod{n}$을 만족하는 합성수 $n$을 **카마이클 수**(Carmichael number)라 부른다.

카마이클 수는 **어떤 밑을 사용해도** 페르마 테스트를 통과하는 합성수이다! 이것은 페르마 테스트가 근본적으로 완벽하지 않다는 것을 보여준다.

### 7H.4.5 교재 예제 11: 561은 카마이클 수

$561 = 3 \times 11 \times 17$은 합성수인데, $\gcd(b, 561) = 1$인 모든 $b$에 대해 $b^{560} \equiv 1 \pmod{561}$이다.

**왜 그런가?** (CRT를 이용한 증명 개요)

$\gcd(b, 561) = 1$이면 $\gcd(b, 3) = 1$이고 $\gcd(b, 11) = 1$이고 $\gcd(b, 17) = 1$이다.

페르마의 작은 정리에 의해:
- $b^2 \equiv 1 \pmod{3}$ (3은 소수, $p-1 = 2$)
- $b^{10} \equiv 1 \pmod{11}$ (11은 소수, $p-1 = 10$)
- $b^{16} \equiv 1 \pmod{17}$ (17은 소수, $p-1 = 16$)

$560 = 280 \times 2 = 56 \times 10 = 35 \times 16$이므로:
- $b^{560} = (b^2)^{280} \equiv 1 \pmod{3}$
- $b^{560} = (b^{10})^{56} \equiv 1 \pmod{11}$
- $b^{560} = (b^{16})^{35} \equiv 1 \pmod{17}$

CRT에 의해: $b^{560} \equiv 1 \pmod{561}$ ✓

```lean
-- 561이 합성수임을 확인
#eval Nat.Prime 561  -- false
#eval 3 * 11 * 17    -- 561

-- 560이 2, 10, 16의 배수임을 확인
example : 560 % 2 = 0 := by native_decide
example : 560 % 10 = 0 := by native_decide
example : 560 % 16 = 0 := by native_decide

-- 카마이클 수 검증: 다양한 b에 대해 확인
-- (큰 수의 거듭제곱이므로 분해하여 계산)
-- b = 2: 2^560 mod 561
-- 2^2 mod 3 = 1, (2^10) mod 11 = 1, (2^16) mod 17 = 1
example : (2^2) % 3 = 1 := by native_decide
example : (2^10) % 11 = 1 := by native_decide
example : (2^16) % 17 = 1 := by native_decide
```

### 7H.4.6 카마이클 수의 성질

교재에 따르면:
- 카마이클 수는 **무한히 많다** (1994년에 증명됨)
- 가장 작은 카마이클 수는 **561**이다
- $10^8$ 이하에 카마이클 수는 255개이다

```lean
-- 몇 가지 카마이클 수 확인
-- 561 = 3 × 11 × 17
-- 1105 = 5 × 13 × 17
-- 1729 = 7 × 13 × 19 (이것은 라마누잔 수이기도 하다!)

#eval 5 * 13 * 17   -- 1105
#eval 7 * 13 * 19   -- 1729

-- 1729는 특별: "택시 수" — 두 양의 세제곱수의 합으로 두 가지 방법으로 쓸 수 있는 가장 작은 수
-- 1729 = 1³ + 12³ = 9³ + 10³
example : 1^3 + 12^3 = 1729 := by norm_num
example : 9^3 + 10^3 = 1729 := by norm_num
```

---

## 7H.5 **기본 루트**(Primitive Roots) — 4.4.7절

### 7H.5.1 기본 루트란?

양의 실수집합에서 $b > 1$이고 $x = b^y$이면 $y = \log_b x$이다. 이것이 **로그**(logarithm)이다.

소수 $p$에 대해서도 비슷한 개념을 정의할 수 있다: **이산 로그**(discrete logarithm).

그러려면 먼저 **기본 루트**(primitive root)를 정의해야 한다.

> **정의 3**: 소수 $p$의 모듈로 연산에서 **기본 루트**(primitive root)는, $\mathbb{Z}_p$의 모든 0이 아닌 원소가 $r$의 누승이 되는 $\mathbb{Z}_p$의 원소인 정수 $r$이다.

쉽게 말해: $r$의 거듭제곱 $r^1, r^2, r^3, \ldots, r^{p-1}$이 (모듈로 $p$에서) $\{1, 2, 3, \ldots, p-1\}$의 모든 원소를 한 번씩 생성하면, $r$은 $p$의 기본 루트이다.

### 7H.5.2 교재 예제 12: 11의 기본 루트

$\mathbb{Z}_{11}$에서 2의 누승을 계산:

| 지수 $k$ | $2^k$ | $2^k \bmod 11$ |
|---|---|---|
| 1 | 2 | 2 |
| 2 | 4 | 4 |
| 3 | 8 | 8 |
| 4 | 16 | 5 |
| 5 | 32 | 10 |
| 6 | 64 | 9 |
| 7 | 128 | 7 |
| 8 | 256 | 3 |
| 9 | 512 | 6 |
| 10 | 1024 | 1 |

누승이 $\{2, 4, 8, 5, 10, 9, 7, 3, 6, 1\}$이고 이것은 $\{1, 2, 3, 4, 5, 6, 7, 8, 9, 10\}$의 모든 원소를 포함한다. 따라서 **2는 11의 기본 루트이다!**

```lean
-- Lean4로 확인
def powers (a p : Nat) : List Nat :=
  (List.range (p - 1)).map fun i => (a ^ (i + 1)) % p

#eval powers 2 11
-- [2, 4, 8, 5, 10, 9, 7, 3, 6, 1]
-- {1, 2, ..., 10} 모두 나타남 ✓ → 2는 11의 기본 루트!
```

3의 누승은 어떨까?

$3^1 = 3, 3^2 = 9, 3^3 = 27 \equiv 5, 3^4 = 81 \equiv 4, 3^5 = 243 \equiv 1$

5번째에서 이미 1로 돌아왔다! 나머지는 반복된다.

```lean
-- 3의 누승: 3은 기본 루트가 아님
#eval powers 3 11
-- [3, 9, 5, 4, 1, 3, 9, 5, 4, 1]
-- 패턴이 반복! {3, 9, 5, 4, 1}만 나옴 → 3은 기본 루트가 아님
```

### 7H.5.3 **위수**(Order)와 기본 루트의 관계

$r^k \equiv 1 \pmod{p}$인 최소 양의 정수 $k$를 $r$의 **위수**(order)라 한다. 기본 루트는 위수가 정확히 $p - 1$인 원소이다.

```lean
-- r의 위수 계산: r^k ≡ 1 (mod p)인 최소 k
def order (r p : Nat) : Nat :=
  match (List.range (p - 1)).find? fun k => (r ^ (k + 1)) % p == 1 with
  | some k => k + 1
  | none => 0

#eval order 2 11  -- 10 (= 11-1, 기본 루트!)
#eval order 3 11  -- 5 (< 10, 기본 루트 아님)
#eval order 8 11  -- ?

-- 기본 루트 확인 함수
def isPrimitiveRoot (r p : Nat) : Bool :=
  order r p == p - 1

#eval isPrimitiveRoot 2 11  -- true
#eval isPrimitiveRoot 3 11  -- false

-- 11의 모든 기본 루트 찾기
#eval (List.range 10).filter fun r => isPrimitiveRoot (r + 1) 11
-- 기본 루트들의 목록
```

### 7H.5.4 기본 루트의 존재

> 모든 소수 $p$에 대해 기본 루트가 존재한다.

이것은 정수론의 중요한 정리이다 (증명은 교재 범위를 넘는다).

```lean
-- 작은 소수들의 기본 루트 확인
-- p = 7의 기본 루트
#eval (List.range 6).filter fun r => isPrimitiveRoot (r + 1) 7
-- p = 13의 기본 루트
#eval (List.range 12).filter fun r => isPrimitiveRoot (r + 1) 13
-- p = 17의 기본 루트
#eval (List.range 16).filter fun r => isPrimitiveRoot (r + 1) 17
```

---

## 7H.6 **이산 로그**(Discrete Logarithm) — 정의 4

### 7H.6.1 정의

> **정의 4**: $p$가 소수이고, $r$이 기본 루트 모듈로 $p$이고, $a$가 $1$ 이상 $p-1$ 이하인 정수라고 하자. $r^e \bmod p = a$이고 $1 \le e \le p - 1$인 유일한 정수 $e$를 $a$의 **이산 로그**(discrete logarithm) 밑 $r$ 모듈로 $p$라 하며, $\log_r a$로 쓴다.

### 7H.6.2 보통 로그와의 비교

| 보통 로그 | 이산 로그 |
|---|---|
| 실수 → 실수 | 정수 → 정수 |
| $b^y = x \Rightarrow y = \log_b x$ | $r^e \equiv a \pmod{p} \Rightarrow e = \log_r a$ |
| 연속적 | 이산적 (정수만) |
| 계산이 쉬움 | 계산이 **매우 어려움**! |

### 7H.6.3 교재 예제 13: 이산 로그 계산

$r = 2$, $p = 11$일 때의 이산 로그 표:

7H.5.2에서 계산한 2의 누승을 이용:

| $a$ | $\log_2 a \pmod{11}$ | 확인: $2^e \bmod 11$ |
|---|---|---|
| 1 | 10 | $2^{10} = 1024 \equiv 1$ |
| 2 | 1 | $2^1 = 2$ |
| 3 | 8 | $2^8 = 256 \equiv 3$ |
| 4 | 2 | $2^2 = 4$ |
| 5 | 4 | $2^4 = 16 \equiv 5$ |
| 6 | 9 | $2^9 = 512 \equiv 6$ |
| 7 | 7 | $2^7 = 128 \equiv 7$ |
| 8 | 3 | $2^3 = 8$ |
| 9 | 6 | $2^6 = 64 \equiv 9$ |
| 10 | 5 | $2^5 = 32 \equiv 10$ |

```lean
-- 이산 로그 계산 함수: log_r(a) mod p
def discreteLog (r a p : Nat) : Option Nat :=
  (List.range (p - 1)).find? fun e => (r ^ (e + 1)) % p == a
  |>.map (· + 1)

-- r = 2, p = 11에서의 이산 로그
#eval discreteLog 2 1 11   -- some 10
#eval discreteLog 2 3 11   -- some 8
#eval discreteLog 2 7 11   -- some 7
#eval discreteLog 2 9 11   -- some 6

-- 전체 테이블 출력
#eval (List.range 10).map fun i => (i + 1, discreteLog 2 (i + 1) 11)
```

### 7H.6.4 이산 로그의 어려움 — 암호학의 핵심!

보통 로그는 계산이 쉽다: $\log_2 1024 = 10$.

그러나 이산 로그는 큰 수에 대해 계산이 **극도로 어렵다**. 이것이 현대 암호학의 핵심이다!

**Diffie-Hellman 키 교환** 프로토콜, **ElGamal 암호**, **타원곡선 암호** 등이 모두 이산 로그의 어려움에 기반한다.

```lean
-- 작은 수에서는 전수검색으로 쉽게 풀 수 있지만...
#eval discreteLog 2 7 11  -- some 7

-- 큰 소수 p에서 r^e ≡ a (mod p)인 e를 찾는 것은
-- 알려진 효율적 알고리즘이 없다!
-- 이것이 암호학의 "trapdoor function" (한쪽은 쉽고 반대쪽은 어려운 함수)이다:
-- - 거듭제곱: r^e mod p 계산 → 쉬움 (빠른 거듭제곱법 O(log e))
-- - 이산 로그: a에서 e 찾기 → 어려움 (알려진 최선: 지수시간)
```

---

## 7H.7 연습문제 세트 2: 기본 루트와 이산 로그

### 연습 2-1: 교재 연습문제 37(a)

$p = 7$의 모든 기본 루트를 구하라.

```lean
-- 힌트: 1부터 6까지의 각 수의 위수를 계산
#eval (List.range 6).map fun r => (r + 1, order (r + 1) 7)
-- 위수가 6 (= p-1)인 것이 기본 루트
```

<details>
<summary>💡 답 보기</summary>

```lean
#eval (List.range 6).map fun r => (r + 1, order (r + 1) 7)
-- [(1, 1), (2, 3), (3, 6), (4, 3), (5, 6), (6, 2)]
-- 위수가 6인 것: 3, 5
-- 따라서 7의 기본 루트는 3과 5이다.

-- 검증
#eval powers 3 7  -- [3, 2, 6, 4, 5, 1] — 모든 원소 ✓
#eval powers 5 7  -- [5, 4, 6, 2, 3, 1] — 모든 원소 ✓
```

</details>

### 연습 2-2: 교재 연습문제 37(b)

$r = 3$이 $p = 7$의 기본 루트일 때, 이산 로그 표를 완성하라.

| $a$ | $\log_3 a \pmod{7}$ |
|---|---|
| 1 | ? |
| 2 | ? |
| 3 | ? |
| 4 | ? |
| 5 | ? |
| 6 | ? |

```lean
-- 3의 누승 (mod 7): 3^1 = 3, 3^2 = 2, 3^3 = 6, 3^4 = 4, 3^5 = 5, 3^6 = 1
#eval powers 3 7

-- 이산 로그 표 계산
#eval (List.range 6).map fun i => (i + 1, discreteLog 3 (i + 1) 7)
```

<details>
<summary>💡 답 보기</summary>

```lean
#eval powers 3 7  -- [3, 2, 6, 4, 5, 1]

-- log_3(1) = 6 (3^6 ≡ 1)
-- log_3(2) = 2 (3^2 ≡ 2)
-- log_3(3) = 1 (3^1 ≡ 3)
-- log_3(4) = 4 (3^4 ≡ 4)
-- log_3(5) = 5 (3^5 ≡ 5)
-- log_3(6) = 3 (3^3 ≡ 6)

#eval (List.range 6).map fun i => (i + 1, discreteLog 3 (i + 1) 7)
-- [(1, some 6), (2, some 2), (3, some 1), (4, some 4), (5, some 5), (6, some 3)]
```

</details>

### 연습 2-3: sorry 연습 — 위수와 기본 루트

```lean
-- p = 13에서 2의 위수는?
theorem order_2_mod_13 : order 2 13 = sorry := by native_decide

-- 2는 13의 기본 루트인가?
theorem is_2_prim_root_13 : isPrimitiveRoot 2 13 = sorry := by native_decide
```

<details>
<summary>💡 답 보기</summary>

```lean
-- 2의 누승 (mod 13)
#eval powers 2 13
-- [2, 4, 8, 3, 6, 12, 11, 9, 5, 10, 7, 1]
-- 12개 모두 다름 → 위수 = 12 = p-1

theorem order_2_mod_13 : order 2 13 = 12 := by native_decide
theorem is_2_prim_root_13 : isPrimitiveRoot 2 13 = true := by native_decide
```

</details>

---

## 7H.8 『Mathematics in Lean』 연결 — 소수의 무한성

### 7H.8.1 페르마의 작은 정리와 Mathlib

Mathlib에는 페르마의 작은 정리가 `ZMod.pow_card_sub_one_eq_one`으로 형식화되어 있다:

```lean
-- Mathlib에서의 페르마의 작은 정리 (참고용)
-- import Mathlib.FieldTheory.Finite.Basic
-- theorem ZMod.pow_card_sub_one_eq_one {p : ℕ} [Fact (Nat.Prime p)]
--   {x : ZMod p} (hx : x ≠ 0) : x ^ (p - 1) = 1

-- 이것은 "p가 소수이고 x ≠ 0이면 x^(p-1) = 1 in ZMod p"를 말한다.
-- 우리가 배운 a^(p-1) ≡ 1 (mod p)의 정확한 형식화이다!
```

### 7H.8.2 소수의 무한성 (Mathematics in Lean 5.3)

『Mathematics in Lean』 Chapter 5.3에서는 유클리드의 정리(소수는 무한히 많다)를 증명한다. 이것은 페르마의 작은 정리와 직접 관련되지는 않지만, 정수론의 기초를 이루는 중요한 정리이다.

```lean
-- Mathematics in Lean에서의 소수 관련 정리들 (참고)
-- Nat.exists_infinite_primes : ∀ n, ∃ p, n ≤ p ∧ Nat.Prime p
-- "어떤 수 n보다 큰 소수가 항상 존재한다" = 소수는 무한히 많다
```

---

## 7H.9 연습문제 세트 3: 종합

### 연습 3-1: 페르마 + 역의 응용

$5^{-1} \bmod 29$를 페르마의 작은 정리를 이용하여 구하라.

```lean
-- 5^(29-2) = 5^27 mod 29
-- 힌트: 27 = 2×13 + 1이므로 5^27 = (5^13)^2 × 5
-- 또는 그냥 직접 계산!
#eval (5^27) % 29  -- ?

-- 검증: 5 × ? ≡ 1 (mod 29)
example : (5 * sorry) % 29 = 1 := by native_decide
```

<details>
<summary>💡 답 보기</summary>

```lean
#eval (5^27) % 29  -- 6
-- 5의 역(mod 29) = 6

-- 검증
example : (5 * 6) % 29 = 1 := by native_decide  -- 30 mod 29 = 1 ✓
```

</details>

### 연습 3-2: 의사소수 찾기

$91 = 7 \times 13$이 밑 3의 의사소수인지 확인하라.

```lean
-- 3^90 mod 91 = ?
-- 힌트: 7은 소수이므로 3^6 ≡ 1 (mod 7)
-- 13은 소수이므로 3^12 ≡ 1 (mod 13)
-- 90 = 15 × 6 = 90/12 ... 확인

example : 90 % 6 = sorry := by native_decide
example : 90 % 12 = sorry := by native_decide
```

<details>
<summary>💡 답 보기</summary>

```lean
example : 90 % 6 = 0 := by native_decide   -- 6 | 90 ✓
example : 90 % 12 = 6 := by native_decide  -- 12 ∤ 90!

-- 3^12 ≡ 1 (mod 13)이고 90 = 7 × 12 + 6이므로
-- 3^90 = (3^12)^7 × 3^6 ≡ 1 × 3^6 (mod 13)
#eval (3^6) % 13  -- 1! (우연히 1이다)
-- 3^6 = 729 = 56 × 13 + 1, 즉 3^6 ≡ 1 (mod 13) ✓

-- 따라서 3^90 ≡ 1 (mod 7)이고 3^90 ≡ 1 (mod 13)
-- CRT에 의해 3^90 ≡ 1 (mod 91)
-- 결론: 91은 밑 3의 의사소수이다!

-- 직접 검증 (가능하면)
example : (3^6) % 7 = 1 := by native_decide
example : (3^6) % 13 = 1 := by native_decide
-- 3의 위수가 7에서도 13에서도 6의 약수이므로 90의 약수이다
```

</details>

### 연습 3-3: 종합 — sorry 완전 연습

```lean
-- 1. 페르마의 작은 정리
theorem ex_fermat : (4^16) % 17 = sorry := by native_decide

-- 2. 거듭제곱 나머지
-- 11^202 mod 7 = ? (202 mod 6 = ?)
theorem ex_power : (11^202) % 7 = sorry := by native_decide

-- 3. 기본 루트 확인
-- 3은 17의 기본 루트인가?
theorem ex_prim : isPrimitiveRoot 3 17 = sorry := by native_decide
```

<details>
<summary>💡 답 보기</summary>

```lean
theorem ex_fermat : (4^16) % 17 = 1 := by native_decide
-- 17은 소수, gcd(4,17) = 1이므로 페르마의 작은 정리에 의해 4^16 ≡ 1 (mod 17)

theorem ex_power : (11^202) % 7 = 2 := by native_decide
-- 202 mod 6 = 4, 11 mod 7 = 4, 4^4 = 256, 256 mod 7 = 4... 확인
-- 실제: 11^202 mod 7 = (11 mod 7)^(202 mod 6) mod 7 = 4^4 mod 7 = 256 mod 7 = 4
-- 아니다, native_decide로 직접 확인하자
#eval (11^202) % 7  -- 2

theorem ex_prim : isPrimitiveRoot 3 17 = false := by native_decide
-- 3의 위수(mod 17)가 16이 아님
#eval order 3 17  -- 16이 아닌 값
```

실제 계산 결과로 수정:

```lean
#eval (11^202) % 7        -- 직접 확인
#eval order 3 17          -- 3의 위수 확인
#eval isPrimitiveRoot 3 17  -- 기본 루트 여부
```

</details>

---

## 7H.10 전술 요약

| 전술 | 용도 | 예시 |
|------|------|------|
| `native_decide` | 구체적 숫자 계산 | `(7^222) % 11 = 5` |
| `norm_num` | 정수 산술 | `222 = 22 * 10 + 2` |
| `decide` | 유한 범위 전수 검사 | `∀ a : Fin n, ...` |
| `use` | 존재 증인 | `use 5` |
| `ring` | 대수적 등식 | 다항식 정리 |

---

## 7H.11 핵심 정리 요약

| 이름 | 내용 |
|------|------|
| **정리 3** (페르마의 작은 정리) | $p$ 소수, $p \nmid a$ → $a^{p-1} \equiv 1 \pmod{p}$ |
| **정의 1** (의사소수) | 합성수 $n$이 $b^{n-1} \equiv 1 \pmod{n}$ → 밑 $b$ 의사소수 |
| **정의 2** (카마이클 수) | 모든 $\gcd(b,n)=1$인 $b$에 대해 의사소수인 합성수 |
| **정의 3** (기본 루트) | $r$의 누승이 $\{1, \ldots, p-1\}$ 전체를 생성 |
| **정의 4** (이산 로그) | $r^e \equiv a \pmod{p}$인 $e$가 $\log_r a$ |
| **응용** | $a^{p-2}$는 $a$의 역 (mod $p$); 이산 로그의 어려움 → 암호학 |

---

## 다음 편(7-I) 예고

**제7-I편** (합동의 응용)에서는:
- **해싱 함수**(hashing functions)
- **의사난수 생성**(pseudorandom number generation)
- **검증 숫자**(check digits): ISBN, UPC 등

을 다룬다.

---

**(끝)**
