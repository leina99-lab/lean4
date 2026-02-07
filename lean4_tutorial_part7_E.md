# Lean4 완전 정복 가이드 — 제7-E편

## **최대공약수**(GCD), **최소공배수**(LCM), **유클리드 알고리즘**(Euclidean Algorithm) 완전 정복

> **교재**: Kenneth H. Rosen, *Discrete Mathematics and Its Applications* 8판 4.3절 (후반부)  
> **참고**: 『Mathematics in Lean』 Chapter 5 Elementary Number Theory  
> **선수 학습**: 제7-D편(소수와 소인수분해)

---

## 7E.0 이 장의 목표

1. **최대공약수**(GCD)의 정의와 계산 — Lean4의 `Nat.gcd`
2. **서로소**(coprime)의 판정 — `Nat.Coprime`
3. **유클리드 알고리즘**(Euclidean algorithm) — 직접 구현하고 Mathlib 버전과 비교
4. **최소공배수**(LCM) — `Nat.lcm`과 gcd·lcm 관계
5. **선형 결합으로서의 gcd** — `gcd(a,b) = sa + tb`
6. **베주의 정리**(Bézout's theorem)와 **확장 유클리드 알고리즘**
7. **합동식에서의 나눗셈** (Rosen 정리 7)

---

## 7E.1 **최대공약수**(Greatest Common Divisor, GCD)

### 7E.1.1 정의 (Rosen 정의 2)

> **정의 2**: a와 b가 0이 아닌 정수라 하자. d | a이고 d | b인 정수 중 가장 큰 d를 a와 b의 **최대공약수**라 하고, gcd(a, b)로 표현한다.

쉽게 말하면: 두 수를 **모두** 나누는 수 중에서 **가장 큰** 수이다.

예를 들어:
- 24의 약수: {1, 2, 3, 4, 6, 8, 12, 24}
- 36의 약수: {1, 2, 3, 4, 6, 9, 12, 18, 36}
- 공약수: {1, 2, 3, 4, 6, 12}
- **최대공약수**: gcd(24, 36) = **12**

### 7E.1.2 Lean4에서 GCD: `Nat.gcd`

```lean
-- Lean4에는 GCD가 내장되어 있다
#check Nat.gcd      -- Nat → Nat → Nat
#check @Nat.gcd_dvd_left   -- Nat.gcd m n ∣ m
#check @Nat.gcd_dvd_right  -- Nat.gcd m n ∣ n

-- 구체적인 값 계산
#eval Nat.gcd 24 36   -- 12
#eval Nat.gcd 17 22   -- 1  (서로소)
#eval Nat.gcd 100 75  -- 25
#eval Nat.gcd 0 5     -- 5  (gcd(0, n) = n)
#eval Nat.gcd 7 0     -- 7  (gcd(n, 0) = n)
```

### 7E.1.3 GCD의 핵심 성질들

```lean
-- 성질 1: gcd(a, b)는 a를 나눈다
#check @Nat.gcd_dvd_left   -- ∀ (m n : Nat), Nat.gcd m n ∣ m

-- 성질 2: gcd(a, b)는 b를 나눈다
#check @Nat.gcd_dvd_right  -- ∀ (m n : Nat), Nat.gcd m n ∣ n

-- 성질 3: d가 a와 b 모두를 나누면, d는 gcd(a,b)를 나눈다
#check Nat.dvd_gcd          -- d ∣ m → d ∣ n → d ∣ Nat.gcd m n

-- 성질 4: gcd(a, b) = gcd(b, a) (교환법칙)
#check Nat.gcd_comm          -- Nat.gcd m n = Nat.gcd n m

-- 성질 5: gcd(a, 0) = a
#check Nat.gcd_zero_right    -- Nat.gcd m 0 = m
```

### 연습 7E.1: GCD 계산 (Rosen 예제 10-11)

```lean
-- 교재 예제 10: gcd(24, 36) = 12
example : Nat.gcd 24 36 = 12 := by norm_num

-- 교재 예제 11: gcd(17, 22) = 1
example : Nat.gcd 17 22 = 1 := by norm_num

-- 연습: 빈칸 채우기
example : Nat.gcd 12 18 = sorry := by norm_num
example : Nat.gcd 100 75 = sorry := by norm_num
example : Nat.gcd 48 36 = sorry := by norm_num
example : Nat.gcd 0 15 = sorry := by norm_num
example : Nat.gcd 7 11 = sorry := by norm_num
```

<details>
<summary>💡 답 보기</summary>

```lean
example : Nat.gcd 12 18 = 6 := by norm_num
example : Nat.gcd 100 75 = 25 := by norm_num
example : Nat.gcd 48 36 = 12 := by norm_num
example : Nat.gcd 0 15 = 15 := by norm_num
example : Nat.gcd 7 11 = 1 := by norm_num   -- 서로소
```

</details>

---

## 7E.2 **서로소**(Coprime) — 복습 및 심화

### 7E.2.1 정의 (Rosen 정의 3)

> **정의 3**: 두 정수 a와 b의 최대공약수가 1이면, a와 b는 **서로소**(relatively prime)라 한다.

### 7E.2.2 **쌍으로 서로소**(Pairwise Coprime) (Rosen 정의 4)

> **정의 4**: 정수 a₁, a₂, ..., aₙ이 **쌍으로 서로소**(pairwise relatively prime)라 함은, 1 ≤ i < j ≤ n인 모든 쌍에 대해 gcd(aᵢ, aⱼ) = 1인 것이다.

```lean
-- Lean4에서 서로소
example : Nat.Coprime 10 21 := by norm_num   -- gcd(10,21) = 1

-- 쌍으로 서로소 확인 (교재 예제 13)
-- 10, 17, 21이 쌍으로 서로소인가?
example : Nat.Coprime 10 17 := by norm_num  -- gcd(10,17) = 1 ✓
example : Nat.Coprime 10 21 := by norm_num  -- gcd(10,21) = 1 ✓
example : Nat.Coprime 17 21 := by norm_num  -- gcd(17,21) = 1 ✓
-- 결론: 세 수 모두 서로 쌍으로 서로소이다

-- 10, 19, 24는 쌍으로 서로소인가?
example : Nat.Coprime 10 19 := by norm_num  -- gcd(10,19) = 1 ✓
example : ¬ Nat.Coprime 10 24 := by norm_num  -- gcd(10,24) = 2 ✗
-- 결론: 10과 24의 gcd가 1이 아니므로, 쌍으로 서로소가 아니다
```

### 연습 7E.2: 서로소 판정 (Rosen 연습문제 16-17 유형)

```lean
-- (a) 21, 34, 55는 쌍으로 서로소인가?
example : Nat.Coprime 21 34 := by (______)
example : Nat.Coprime 21 55 := by (______)
example : Nat.Coprime 34 55 := by (______)
-- 결론: (______)

-- (b) 14, 17, 85는 쌍으로 서로소인가?
example : Nat.Coprime 14 17 := by (______)
example : Nat.Coprime 14 85 := by (______)
-- 결론: (______)
```

<details>
<summary>💡 답 보기</summary>

```lean
-- (a) 21, 34, 55: 쌍으로 서로소 확인
example : Nat.Coprime 21 34 := by norm_num  -- gcd = 1 ✓
example : Nat.Coprime 21 55 := by norm_num  -- gcd = 1 ✓
example : Nat.Coprime 34 55 := by norm_num  -- gcd = 1 ✓
-- 결론: 쌍으로 서로소이다!

-- (b) 14, 17, 85: 쌍으로 서로소가 아님
example : Nat.Coprime 14 17 := by norm_num  -- gcd = 1 ✓
-- 하지만:
example : ¬ Nat.Coprime 14 85 := by norm_num  -- gcd(14,85) = 7 ✗
-- 결론: 14와 85의 gcd가 7이므로 쌍으로 서로소가 아니다
```

</details>

---

## 7E.3 **소인수분해를 이용한 GCD/LCM 계산**

### 7E.3.1 소인수분해로 GCD 구하기

a와 b의 소인수분해가 주어지면, 각 소수의 지수 중 **작은 것**을 택하면 gcd가 된다.

예 (교재 예제 14):
- 120 = 2³ · 3 · 5
- 500 = 2² · 5³
- gcd(120, 500) = 2^min(3,2) · 3^min(1,0) · 5^min(1,3) = 2² · 3⁰ · 5¹ = 4 · 1 · 5 = **20**

```lean
-- Lean4로 확인
example : Nat.gcd 120 500 = 20 := by norm_num

-- 소인수분해 확인
#eval Nat.primeFactorsList 120   -- [2, 2, 2, 3, 5]
#eval Nat.primeFactorsList 500   -- [2, 2, 5, 5, 5]

-- 각 소수의 지수 확인
#eval Nat.factorization 120 2    -- 3
#eval Nat.factorization 120 3    -- 1
#eval Nat.factorization 120 5    -- 1
#eval Nat.factorization 500 2    -- 2
#eval Nat.factorization 500 5    -- 3
```

### 7E.3.2 소인수분해로 LCM 구하기 (Rosen 정의 5)

> **정의 5**: 양의 정수 a와 b의 **최소공배수**(least common multiple)는 a와 b 모두로 나눌 수 있는 가장 작은 양의 정수이다. lcm(a, b)로 표현한다.

소인수분해에서 각 소수의 지수 중 **큰 것**을 택하면 lcm이 된다.

```lean
-- Lean4에서 LCM
#check Nat.lcm
#eval Nat.lcm 120 500   -- 3000

-- 교재 예제 15
-- lcm(2³·3⁵·7², 2⁴·3³) = 2⁴·3⁵·7²
-- = 16 · 243 · 49 = 190512
-- 직접 확인:
#eval Nat.lcm (2^3 * 3^5 * 7^2) (2^4 * 3^3)  -- 190512
```

### 7E.3.3 GCD와 LCM의 관계 (Rosen 정리 5)

> **정리 5**: a와 b를 양의 정수라 하자. 그러면 ab = gcd(a, b) · lcm(a, b)

```lean
-- 이 관계를 구체적인 수로 확인
example : 120 * 500 = Nat.gcd 120 500 * Nat.lcm 120 500 := by norm_num
-- 120 * 500 = 60000 = 20 * 3000 ✓
```

### 연습 7E.3: GCD/LCM 계산 (Rosen 연습문제 24-28 유형)

```lean
-- (a) gcd와 lcm 계산
example : Nat.gcd 12 18 = sorry := by norm_num
example : Nat.lcm 12 18 = sorry := by norm_num
-- 검증: 12 * 18 = gcd * lcm?
example : 12 * 18 = Nat.gcd 12 18 * Nat.lcm 12 18 := by norm_num

-- (b) gcd(100, 75) 계산
example : Nat.gcd 100 75 = sorry := by norm_num
example : Nat.lcm 100 75 = sorry := by norm_num

-- (c) gcd(0, 51) 계산
example : Nat.gcd 0 51 = sorry := by norm_num

-- (d) gcd(17, 17^17) 계산
-- 힌트: 17은 소수이고 17 | 17^17이므로...
example : Nat.gcd 17 (17^3) = sorry := by norm_num
```

<details>
<summary>💡 답 보기</summary>

```lean
-- (a) gcd(12,18) = 6, lcm(12,18) = 36
example : Nat.gcd 12 18 = 6 := by norm_num
example : Nat.lcm 12 18 = 36 := by norm_num

-- (b) gcd(100,75) = 25, lcm(100,75) = 300
example : Nat.gcd 100 75 = 25 := by norm_num
example : Nat.lcm 100 75 = 300 := by norm_num

-- (c) gcd(0, 51) = 51
example : Nat.gcd 0 51 = 51 := by norm_num

-- (d) gcd(17, 17³) = 17
example : Nat.gcd 17 (17^3) = 17 := by norm_num
```

</details>

---

## 7E.4 **유클리드 알고리즘**(Euclidean Algorithm)

### 7E.4.1 왜 유클리드 알고리즘이 필요한가?

소인수분해를 이용한 GCD 계산은 이론적으로 명확하지만, 큰 수의 소인수분해는 매우 어렵다. **유클리드 알고리즘**은 소인수분해 없이 GCD를 효율적으로 계산한다.

### 7E.4.2 핵심 보조정리 (Rosen 보조정리 1)

> **보조정리 1**: a, b, q, r이 정수이고 a = bq + r이면, gcd(a, b) = gcd(b, r)이다.

이것이 유클리드 알고리즘의 핵심이다! "나눗셈의 나머지로 바꾸어도 gcd가 변하지 않는다."

```lean
-- Lean4에서 이 보조정리에 해당하는 것
-- gcd(a, b) = gcd(b, a % b)
-- 이것이 Nat.gcd의 정의 자체이다!

-- 구체적 예: gcd(287, 91)
-- 287 = 91 × 3 + 14이므로 gcd(287, 91) = gcd(91, 14)
-- 91 = 14 × 6 + 7이므로 gcd(91, 14) = gcd(14, 7)
-- 14 = 7 × 2 + 0이므로 gcd(14, 7) = gcd(7, 0) = 7
example : Nat.gcd 287 91 = 7 := by norm_num

-- 각 단계를 확인
example : 287 % 91 = 14 := by norm_num
example : 91 % 14 = 7 := by norm_num
example : 14 % 7 = 0 := by norm_num
```

### 7E.4.3 유클리드 알고리즘을 직접 구현

```lean
-- 유클리드 알고리즘 (교재 알고리즘 1과 동일)
def myGcd : Nat → Nat → Nat
  | a, 0     => a
  | a, b + 1 => myGcd (b + 1) (a % (b + 1))

-- 테스트
#eval myGcd 287 91    -- 7
#eval myGcd 414 662   -- 2
#eval myGcd 252 198   -- 18
```

### 7E.4.4 교재 예제 16 — gcd(414, 662) 상세 추적

교재의 예제를 단계별로 추적해 보자:

```lean
-- gcd(414, 662)를 유클리드 알고리즘으로 계산
-- 주의: gcd(414, 662) = gcd(662, 414)이므로
-- 662 = 414 × 1 + 248
-- 414 = 248 × 1 + 166
-- 248 = 166 × 1 + 82
-- 166 = 82 × 2 + 2
-- 82 = 2 × 41 + 0
-- 따라서 gcd(414, 662) = 2

-- 각 단계 확인
example : 662 % 414 = 248 := by norm_num
example : 414 % 248 = 166 := by norm_num
example : 248 % 166 = 82 := by norm_num
example : 166 % 82 = 2 := by norm_num
example : 82 % 2 = 0 := by norm_num

-- 최종 결과
example : Nat.gcd 414 662 = 2 := by norm_num
```

### 7E.4.5 유클리드 알고리즘의 추적 함수

알고리즘의 각 단계를 출력하는 버전:

```lean
-- 추적 기능이 있는 유클리드 알고리즘
def gcdTrace : Nat → Nat → List (Nat × Nat) → List (Nat × Nat)
  | a, 0, acc     => acc ++ [(a, 0)]
  | a, b + 1, acc => gcdTrace (b + 1) (a % (b + 1)) (acc ++ [(a, b + 1)])

-- 사용 예
#eval gcdTrace 414 662 []
-- [(414, 662), (662, 414), (414, 248), (248, 166), (166, 82), (82, 2), (2, 0)]
-- 마지막 단계의 첫 번째 원소가 gcd = 2
```

### 연습 7E.4: 유클리드 알고리즘 추적 (Rosen 연습문제 32-33 유형)

```lean
-- (a) gcd(12, 18) — 단계별 추적
example : 18 % 12 = sorry := by norm_num
example : 12 % (______) = 0 := by norm_num
example : Nat.gcd 12 18 = sorry := by norm_num

-- (b) gcd(111, 201) — 단계별 추적
example : 201 % 111 = sorry := by norm_num
example : 111 % (______) = sorry := by norm_num
-- 계속해서 나머지가 0이 될 때까지...
example : Nat.gcd 111 201 = sorry := by norm_num

-- (c) gcd(1001, 1331) — 단계별 추적
example : Nat.gcd 1001 1331 = sorry := by norm_num
```

<details>
<summary>💡 답 보기</summary>

```lean
-- (a) gcd(12, 18)
-- 18 = 12 × 1 + 6
-- 12 = 6 × 2 + 0
example : 18 % 12 = 6 := by norm_num
example : 12 % 6 = 0 := by norm_num
example : Nat.gcd 12 18 = 6 := by norm_num

-- (b) gcd(111, 201)
-- 201 = 111 × 1 + 90
-- 111 = 90 × 1 + 21
-- 90 = 21 × 4 + 6
-- 21 = 6 × 3 + 3
-- 6 = 3 × 2 + 0
example : 201 % 111 = 90 := by norm_num
example : 111 % 90 = 21 := by norm_num
example : 90 % 21 = 6 := by norm_num
example : 21 % 6 = 3 := by norm_num
example : 6 % 3 = 0 := by norm_num
example : Nat.gcd 111 201 = 3 := by norm_num

-- (c) gcd(1001, 1331)
-- 1331 = 1001 × 1 + 330
-- 1001 = 330 × 3 + 11
-- 330 = 11 × 30 + 0
example : Nat.gcd 1001 1331 = 11 := by norm_num
```

</details>

---

## 7E.5 **베주의 정리**(Bézout's Theorem)와 **선형 결합**(Linear Combination)

### 7E.5.1 정리 내용 (Rosen 정리 6)

> **정리 6** (베주의 정리): a와 b가 양의 정수이면, gcd(a, b) = sa + tb인 정수 s와 t가 존재한다.

이 s와 t를 **베주 계수**(Bézout coefficients)라 한다.

예: gcd(6, 14) = 2이고, 2 = (-2) · 6 + 1 · 14이므로, s = -2, t = 1이다.

### 7E.5.2 Lean4에서 베주의 정리

```lean
-- Lean4에서 베주의 정리
-- 주의: Nat에서는 음수가 없으므로, 정수(Int) 버전을 사용해야 한다
#check Int.gcd_eq_gcd_ab
-- 정수에서: (↑(Int.gcd a b) : ℤ) = a * Int.gcdA a b + b * Int.gcdB a b

-- 자연수에서의 GCD 확인
#eval Nat.gcd 252 198   -- 18
#eval Nat.gcd 6 14      -- 2
```

### 7E.5.3 교재 예제 17 — 선형 결합으로 gcd 표현

gcd(252, 198) = 18을 252와 198의 선형 결합으로 표현해 보자.

유클리드 알고리즘의 단계를 거꾸로 올라간다:

```
252 = 198 × 1 + 54
198 = 54 × 3 + 36
54 = 36 × 1 + 18
36 = 18 × 2 + 0
```

마지막에서 두 번째 나눗셈에서 시작:
1. 18 = 54 - 1 · 36
2. 36 = 198 - 3 · 54를 대입: 18 = 54 - 1 · (198 - 3 · 54) = 4 · 54 - 1 · 198
3. 54 = 252 - 1 · 198을 대입: 18 = 4 · (252 - 1 · 198) - 1 · 198 = 4 · 252 - 5 · 198

```lean
-- 검증: 18 = 4 × 252 - 5 × 198
-- 자연수에서는 뺄셈이 까다우므로 정수로 확인
example : (18 : Int) = 4 * 252 - 5 * 198 := by norm_num

-- 또는 양수 형태로:
-- 4 × 252 = 18 + 5 × 198
example : 4 * 252 = 18 + 5 * 198 := by norm_num
```

### 연습 7E.5: 선형 결합 (Rosen 연습문제 39-40 유형)

```lean
-- (a) gcd(10, 11)을 선형 결합으로 표현
-- gcd(10, 11) = 1
-- 11 = 10 × 1 + 1이므로 1 = 11 - 10 = (-1) × 10 + 1 × 11
example : (1 : Int) = (-1) * 10 + 1 * 11 := by norm_num

-- (b) gcd(21, 44)을 선형 결합으로 표현 — sorry
-- gcd(21, 44) = 1
-- 힌트: 유클리드 알고리즘을 거꾸로 올라가시오
example : Nat.gcd 21 44 = 1 := by norm_num
example : (1 : Int) = sorry * 21 + sorry * 44 := by norm_num
```

<details>
<summary>💡 답 보기</summary>

```lean
-- (b) gcd(21, 44) = 1
-- 유클리드 알고리즘:
-- 44 = 21 × 2 + 2
-- 21 = 2 × 10 + 1
-- 2 = 1 × 2 + 0
-- 거꾸로:
-- 1 = 21 - 2 × 10
-- 2 = 44 - 21 × 2를 대입:
-- 1 = 21 - (44 - 21 × 2) × 10 = 21 - 10 × 44 + 20 × 21 = 21 × 21 - 10 × 44
example : (1 : Int) = 21 * 21 + (-10) * 44 := by norm_num
```

</details>

---

## 7E.6 **확장 유클리드 알고리즘**(Extended Euclidean Algorithm)

### 7E.6.1 아이디어

유클리드 알고리즘을 한 번 실행하면서 동시에 베주 계수 s, t도 계산하는 방법이다. 별도로 거꾸로 올라갈 필요가 없다.

교재의 공식:
- 초기값: s₀ = 1, s₁ = 0, t₀ = 0, t₁ = 1
- 점화식: sⱼ = sⱼ₋₂ - qⱼ₋₁ · sⱼ₋₁, tⱼ = tⱼ₋₂ - qⱼ₋₁ · tⱼ₋₁

### 7E.6.2 Lean4 구현

```lean
-- 확장 유클리드 알고리즘 (정수 버전)
-- 반환값: (gcd, s, t) 여기서 gcd = s*a + t*b
def extGcd : Int → Int → (Int × Int × Int)
  | a, 0 => (a, 1, 0)
  | a, b =>
    let (g, s, t) := extGcd b (a % b)
    (g, t, s - (a / b) * t)

-- 테스트: gcd(252, 198) = 18 = 4*252 + (-5)*198
#eval extGcd 252 198   -- (18, 4, -5)

-- 테스트: gcd(414, 662) = 2
#eval extGcd 414 662   -- (2, ?, ?)
```

### 7E.6.3 교재 예제 18 — 확장 유클리드 알고리즘 추적

gcd(252, 198) = 18을 확장 유클리드 알고리즘으로 구한다.

유클리드 알고리즘 단계: 몫 q₁ = 1, q₂ = 3, q₃ = 1, q₄ = 2

확장 부분:
| j | rⱼ | rⱼ₊₁ | qⱼ₊₁ | sⱼ | tⱼ |
|---|-----|------|------|----|----|
| 0 | 252 | 198  | 1    | 1  | 0  |
| 1 | 198 | 54   | 3    | 0  | 1  |
| 2 | 54  | 36   | 1    | 1  | -1 |
| 3 | 36  | 18   | 2    | -3 | 4  |
| 4 |     |      |      | 4  | -5 |

결과: 18 = 4 · 252 + (-5) · 198

```lean
-- 검증
example : (18 : Int) = 4 * 252 + (-5) * 198 := by norm_num
```

### 연습 7E.6: 확장 유클리드 알고리즘 (sorry 식)

```lean
-- (a) gcd(26, 91)을 선형 결합으로 표현
#eval extGcd 26 91   -- 결과 확인
example : Nat.gcd 26 91 = sorry := by norm_num
-- gcd = s * 26 + t * 91
example : (Nat.gcd 26 91 : Int) = sorry * 26 + sorry * 91 := by norm_num

-- (b) gcd(144, 89)를 선형 결합으로 표현
#eval extGcd 144 89   -- 결과 확인
example : Nat.gcd 144 89 = sorry := by norm_num
example : (Nat.gcd 144 89 : Int) = sorry * 144 + sorry * 89 := by norm_num
```

<details>
<summary>💡 답 보기</summary>

```lean
-- (a) gcd(26, 91) = 13
-- 91 = 26 × 3 + 13
-- 26 = 13 × 2 + 0
-- 따라서 13 = 91 - 26 × 3 = (-3) × 26 + 1 × 91
example : Nat.gcd 26 91 = 13 := by norm_num
example : (Nat.gcd 26 91 : Int) = (-3) * 26 + 1 * 91 := by norm_num

-- (b) gcd(144, 89) = 1
-- #eval extGcd 144 89 → (1, 34, -55)
-- 1 = 34 × 144 + (-55) × 89
example : Nat.gcd 144 89 = 1 := by norm_num
example : (Nat.gcd 144 89 : Int) = 34 * 144 + (-55) * 89 := by norm_num
```

</details>

---

## 7E.7 합동식에서의 소거 (Rosen 정리 7)

### 7E.7.1 정리 내용

> **정리 7**: m이 양의 정수이고 a, b, c를 정수라 하자. ac ≡ bc (mod m)이고 gcd(c, m) = 1이면, a ≡ b (mod m)이다.

핵심: 합동식의 양변을 c로 나눌 수 있으려면, c와 m이 **서로소**여야 한다!

```lean
-- 예: 14 ≡ 8 (mod 6)이고, 양변을 2로 나누면 7 ≡ 4 (mod 6)인가?
-- 14/2 = 7, 8/2 = 4
-- 7 % 6 = 1, 4 % 6 = 4
-- 1 ≠ 4이므로 성립하지 않는다!
-- 왜? gcd(2, 6) = 2 ≠ 1이기 때문이다

example : 14 % 6 = 8 % 6 := by norm_num  -- 14 ≡ 8 (mod 6) ✓
example : ¬ (7 % 6 = 4 % 6) := by norm_num  -- 7 ≢ 4 (mod 6) ✗

-- 반면: 15 ≡ 9 (mod 6)이고 gcd(3, 6) = 3 ≠ 1이므로 소거 불가
-- 하지만: 10 ≡ 25 (mod 5)이고 gcd(5, 5) = 5 ≠ 1이므로 역시 소거 불가

-- 올바른 예: 21 ≡ 9 (mod 6)이고 gcd(3, 6) = 3...
-- 정리 7은 gcd(c, m) = 1인 경우만 보장한다
-- 즉 서로소일 때만 안전하게 소거할 수 있다

-- 서로소인 예: 35 ≡ 14 (mod 7)이고 7로 나누면... (7과 7의 gcd는 7이므로 불가)
-- 올바른 예: 15 ≡ 25 (mod 10)이고 5로 나누고 싶다면
-- gcd(5, 10) = 5 ≠ 1이므로 직접 소거는 안된다

-- 정리 7이 적용되는 올바른 예:
-- 3 × 7 ≡ 3 × 2 (mod 5)이고 gcd(3, 5) = 1이므로
-- 7 ≡ 2 (mod 5) ✓
example : (3 * 7) % 5 = (3 * 2) % 5 := by norm_num  -- 21 % 5 = 6 % 5 = 1
example : 7 % 5 = 2 % 5 := by norm_num  -- 2 = 2 ✓
```

### 연습 7E.7: 합동식 소거

```lean
-- 5 × 13 ≡ 5 × 3 (mod 10)이고 gcd(5, 10) = ?
-- 소거 가능한가?
example : Nat.gcd 5 10 = sorry := by norm_num
-- 답: gcd = 5 ≠ 1이므로 소거 불가능!

-- 7 × 4 ≡ 7 × 1 (mod 3)이고 gcd(7, 3) = ?
-- 소거 가능한가?
example : Nat.gcd 7 3 = sorry := by norm_num
-- gcd = 1이므로 소거 가능!
-- 따라서 4 ≡ 1 (mod 3)
example : 4 % 3 = 1 % 3 := by norm_num  -- 1 = 1 ✓
```

<details>
<summary>💡 답 보기</summary>

```lean
-- 첫 번째: gcd(5, 10) = 5, 소거 불가
example : Nat.gcd 5 10 = 5 := by norm_num

-- 두 번째: gcd(7, 3) = 1, 소거 가능
example : Nat.gcd 7 3 = 1 := by norm_num
```

</details>

---

## 7E.8 종합 연습문제

### 연습 7E.8: GCD 계산 (Rosen 연습문제 32)

```lean
-- 유클리드 알고리즘을 사용하여 다음을 계산하시오
-- (a) gcd(1, 5)
theorem ex32a : Nat.gcd 1 5 = sorry := by norm_num

-- (b) gcd(100, 101)
theorem ex32b : Nat.gcd 100 101 = sorry := by norm_num

-- (c) gcd(123, 277)
theorem ex32c : Nat.gcd 123 277 = sorry := by norm_num

-- (d) gcd(1529, 14039)
theorem ex32d : Nat.gcd 1529 14039 = sorry := by norm_num

-- (e) gcd(1529, 14038)
theorem ex32e : Nat.gcd 1529 14038 = sorry := by norm_num
```

<details>
<summary>💡 답 보기</summary>

```lean
-- (a) gcd(1, 5) = 1 (1은 모든 수와 서로소)
theorem ex32a : Nat.gcd 1 5 = 1 := by norm_num

-- (b) gcd(100, 101) = 1 (연속된 두 수는 항상 서로소)
theorem ex32b : Nat.gcd 100 101 = 1 := by norm_num

-- (c) gcd(123, 277) = 1
theorem ex32c : Nat.gcd 123 277 = 1 := by norm_num

-- (d) gcd(1529, 14039) = 139
-- 14039 = 1529 × 9 + 278
-- 1529 = 278 × 5 + 139
-- 278 = 139 × 2 + 0
theorem ex32d : Nat.gcd 1529 14039 = 139 := by norm_num

-- (e) gcd(1529, 14038) = 1
theorem ex32e : Nat.gcd 1529 14038 = 1 := by norm_num
```

</details>

### 연습 7E.9: LCM과 GCD × LCM = ab 관계 (Rosen 연습문제 28)

```lean
-- gcd(1000, 625)를 구하고 gcd × lcm = 1000 × 625을 검증
theorem ex28_gcd : Nat.gcd 1000 625 = sorry := by norm_num
theorem ex28_lcm : Nat.lcm 1000 625 = sorry := by norm_num
theorem ex28_verify : Nat.gcd 1000 625 * Nat.lcm 1000 625 = 1000 * 625 := by norm_num
```

<details>
<summary>💡 답 보기</summary>

```lean
-- 1000 = 2³ × 5³, 625 = 5⁴
-- gcd = 5³ = 125
-- lcm = 2³ × 5⁴ = 8 × 625 = 5000
-- 125 × 5000 = 625000 = 1000 × 625 ✓
theorem ex28_gcd : Nat.gcd 1000 625 = 125 := by norm_num
theorem ex28_lcm : Nat.lcm 1000 625 = 5000 := by norm_num
theorem ex28_verify : Nat.gcd 1000 625 * Nat.lcm 1000 625 = 1000 * 625 := by norm_num
```

</details>

### 연습 7E.10: GCD의 성질 증명 (sorry 식)

```lean
-- GCD의 교환법칙
theorem gcd_comm_example (a b : Nat) : Nat.gcd a b = Nat.gcd b a := by
  sorry

-- gcd(a, 0) = a
theorem gcd_zero (a : Nat) : Nat.gcd a 0 = a := by
  sorry

-- gcd가 양쪽 모두를 나눔
theorem gcd_dvd_example (a b : Nat) : Nat.gcd a b ∣ a ∧ Nat.gcd a b ∣ b := by
  sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
-- GCD의 교환법칙
theorem gcd_comm_example (a b : Nat) : Nat.gcd a b = Nat.gcd b a := by
  exact Nat.gcd_comm a b

-- gcd(a, 0) = a
theorem gcd_zero (a : Nat) : Nat.gcd a 0 = a := by
  exact Nat.gcd_zero_right a

-- gcd가 양쪽 모두를 나눔
theorem gcd_dvd_example (a b : Nat) : Nat.gcd a b ∣ a ∧ Nat.gcd a b ∣ b := by
  constructor
  · exact Nat.gcd_dvd_left a b
  · exact Nat.gcd_dvd_right a b
```

**설명**: 이 증명들은 Mathlib에 이미 있는 정리를 직접 적용한 것이다. `exact` 전술로 라이브러리 정리를 바로 사용할 수 있다.

</details>

---

## 7E.9 전술 및 라이브러리 정리 요약

### 이 장에서 새로 배운 전술 & 함수

| 이름 | 용도 | 예시 |
|------|------|------|
| `Nat.gcd` | 최대공약수 계산 | `Nat.gcd 12 18 = 6` |
| `Nat.lcm` | 최소공배수 계산 | `Nat.lcm 12 18 = 36` |
| `Nat.Coprime` | 서로소 판정 | `Nat.Coprime 7 10` |
| `Nat.gcd_dvd_left` | gcd ∣ 왼쪽 | `Nat.gcd m n ∣ m` |
| `Nat.gcd_dvd_right` | gcd ∣ 오른쪽 | `Nat.gcd m n ∣ n` |
| `Nat.dvd_gcd` | gcd의 최대성 | `d ∣ m → d ∣ n → d ∣ gcd m n` |
| `Nat.gcd_comm` | gcd 교환법칙 | `gcd m n = gcd n m` |
| `Nat.gcd_zero_right` | gcd(a,0) = a | `Nat.gcd a 0 = a` |
| `Int.gcd_eq_gcd_ab` | 베주의 정리 | `gcd = s*a + t*b` |

### 이전 장 전술 (복습)

| 전술 | 용도 |
|------|------|
| `norm_num` | 구체적 수치 계산 |
| `omega` | 자연수/정수 선형 산술 |
| `exact` | 정확한 증거 제시 |
| `constructor` | ∧ 또는 ↔ 분리 |
| `obtain` | 존재 명제 분해 |
| `by_contra` | 귀류법 |
| `rw` | 치환(슈퍼포지션) |

---

## 7E.10 핵심 정리 요약

1. **최대공약수**(GCD): 두 수를 모두 나누는 수 중 가장 큰 수. Lean4에서 `Nat.gcd`.
2. **서로소**(coprime): gcd = 1. Lean4에서 `Nat.Coprime`.
3. **유클리드 알고리즘**: gcd(a, b) = gcd(b, a mod b)를 반복. O(log b) 시간.
4. **최소공배수**(LCM): 두 수로 모두 나누어떨어지는 가장 작은 수. ab = gcd · lcm.
5. **베주의 정리**: gcd(a,b) = sa + tb인 s, t가 존재한다.
6. **합동식 소거**: ac ≡ bc (mod m)에서 gcd(c,m) = 1이면 a ≡ b (mod m).

---

## 다음 편 예고

**제7-F편** (합동 풀기, 4.4절)에서는:
- 역모듈로(modular inverse) — ax ≡ 1 (mod m) 풀기
- 중국인의 나머지 정리(Chinese Remainder Theorem)
- 페르마의 소정리(Fermat's little theorem)

를 다룬다.

---

**(끝)**
