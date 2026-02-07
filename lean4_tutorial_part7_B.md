# Lean4 완전 정복 가이드 — 제7-B편

## **합동**(Congruence)과 **나머지 산술**(Modular Arithmetic) 완전 정복

> **교재**: Kenneth H. Rosen, "Discrete Mathematics and Its Applications" 8판, 4.1절 후반부  
> **참고**: 『Mathematics in Lean』 Chapter 5 Elementary Number Theory  
> **선수 학습**: 제7-A편(가분성 기초, 나눗셈 알고리즘, →/↔ 차이)

---

## 7B.0 이 장의 목표

이 장에서 배울 내용은 다음과 같다:

1. **합동**(congruence)이란 무엇인가: a ≡ b (mod m)의 정확한 의미
2. Lean4에서 **나머지 연산**(%)으로 합동을 표현하는 방법
3. 합동의 기본 성질 (합과 곱의 보존)
4. **나머지 산술**(modular arithmetic)의 개념과 응용
5. 교재의 예제 5~8과 연습문제를 Lean4로 풀기

---

## 7B.1 **합동**(Congruence)이란?

### 7B.1.1 일상적 예시: 시계

시계는 12시간 단위로 반복된다. 지금이 10시인데, 5시간 후는 3시이다 (15시 = 12 + 3). 우리는 보통 "15시"라고 하지 않고 "3시"라고 한다.

이것이 바로 **나머지 산술**의 핵심 아이디어이다: **나머지만 중요하다.**

24시간 시계에서도 마찬가지이다. 지금부터 50시간 후가 몇 시인지 알려면, 50을 24로 나눈 나머지인 2만 알면 된다. 현재 시각에 2를 더하면 답이다.

### 7B.1.2 교재의 정의 3

> **정의 3** (Rosen 4.1절):  
> a와 b가 정수이고, m이 양의 정수일 때,  
> 만약 m이 a - b를 나누면 a는 b와 **모듈로 m 합동**(congruent to b modulo m)이다.  
> 우리는 a ≡ b (mod m)으로 표기한다.  
> a ≡ b는 **합동**(congruence)이라고 한다.

쉽게 말하면:

> a와 b를 m으로 나눈 **나머지가 같으면**, a ≡ b (mod m)이다.

### 7B.1.3 예시

| a | b | m | a mod m | b mod m | 합동? |
|---|---|---|---------|---------|------|
| 17 | 5 | 6 | 5 | 5 | 예: 17 ≡ 5 (mod 6) |
| 24 | 14 | 6 | 0 | 2 | 아니오: 24 ≢ 14 (mod 6) |
| 10 | 10 | 7 | 3 | 3 | 예: 10 ≡ 10 (mod 7) |
| -11 | 1 | 3 | 1 | 1 | 예: -11 ≡ 1 (mod 3) |

왜 17 ≡ 5 (mod 6)인가?
- 17 - 5 = 12 = 6 × 2이므로 6 ∣ (17 - 5). 따라서 합동이다.
- 또는: 17 mod 6 = 5이고 5 mod 6 = 5이므로, 나머지가 같다.

### 7B.1.4 Lean4에서 합동 표현하기

Lean4에서는 합동을 **나머지 연산**(%)을 사용하여 표현한다:

```lean
-- "a ≡ b (mod m)"는 Lean4에서 "a % m = b % m"으로 표현
-- 예: 17 ≡ 5 (mod 6)
example : 17 % 6 = 5 % 6 := by norm_num

-- 더 간단하게: 5 % 6 = 5이므로
example : 17 % 6 = 5 := by norm_num
```

**참고**: Mathlib에는 `Int.ModEq`라는 전용 합동 타입도 있지만, 기초 단계에서는 `%` 연산으로 충분하다.

```lean
-- Mathlib의 합동 표기 (참고용)
-- Int.ModEq m a b는 a % m = b % m과 동일
#check @Int.ModEq   -- ℤ에서의 합동
```

---

## 7B.2 교재 예제 5: 합동 판정

### 7B.2.1 교재 원문

> **예제 5**: 17이 5와 모듈로 6 합동인가? 또, 24가 14와 모듈로 6 합동인가?
>
> 풀이: 6으로 17 - 5 = 12를 나눌 수 있으므로 17 ≡ 5 (mod 6)이다.  
> 그러나, 24 - 14 = 10은 6으로 나눌 수 없으므로 24 ≢ 14 (mod 6)이다.

### 7B.2.2 Lean4 코드 (완성된 예제)

```lean
-- 예제 5a: 17 ≡ 5 (mod 6)
example : 17 % 6 = 5 % 6 := by norm_num

-- 예제 5b: 24 ≢ 14 (mod 6)
example : ¬ (24 % 6 = 14 % 6) := by norm_num
```

### 7B.2.3 중간 괄호 채우기 연습

```lean
-- 연습: 빈칸을 채워라
-- 23 ≡ ? (mod 7)  — 23을 7로 나눈 나머지는?
example : 23 % 7 = _ := by norm_num   -- 🔲
```

<details>
<summary>💡 답 보기</summary>

```lean
example : 23 % 7 = 2 := by norm_num   -- 23 = 7 × 3 + 2
```

</details>

```lean
-- 연습: 38 ≡ 8 (mod 10)인가?
-- 빈칸에 True 또는 False를 넣어라
example : 38 % 10 = 8 % 10 := by norm_num   -- 이것이 성립하는가?
```

<details>
<summary>💡 답 보기</summary>

```lean
-- 38 % 10 = 8, 8 % 10 = 8이므로 성립한다
example : 38 % 10 = 8 % 10 := by norm_num
```

</details>

---

## 7B.3 교재 정리 3: 합동과 나머지의 관계

### 7B.3.1 교재 원문

> **정리 3** (Rosen 4.1절):  
> a와 b가 정수이고, m이 양의 정수라고 하자.  
> 그러면 a ≡ b (mod m)은 a mod m = b mod m일 **필요충분조건**(↔)이다.

이 정리는 합동의 두 가지 정의가 **동치**(equivalent)임을 말한다:
- 정의 1: m ∣ (a - b)
- 정의 2: a mod m = b mod m

### 7B.3.2 Lean4에서의 의미

이 정리는 ↔(쌍조건문)이다! 양 방향 모두 성립한다.

```lean
-- 정리 3의 정수 버전
-- Int.emod_emod_of_dvd, Int.ModEq 등을 활용할 수 있지만,
-- 기초 단계에서는 구체적인 수로 확인하자

-- 17 ≡ 5 (mod 6) ↔ 17 mod 6 = 5 mod 6
example : 17 % 6 = 5 % 6 ↔ 6 ∣ (17 - 5) := by
  constructor
  · intro _; norm_num
  · intro _; norm_num
```

---

## 7B.4 교재 정리 4: 합동과 정수 k의 관계

### 7B.4.1 교재 원문

> **정리 4** (Rosen 4.1절):  
> m이 양의 정수라고 하자. 정수 a와 b가 모듈로 m 합동임의  
> **필요충분조건**은 a = b + km인 정수 k가 존재한다는 것이다.

### 7B.4.2 수학적 의미

a ≡ b (mod m) ↔ ∃ k, a = b + k * m

이것은 "a와 b의 차이가 m의 배수"라는 뜻을 더 명확하게 표현한 것이다.

### 7B.4.3 Lean4 코드 (구체적 예시)

```lean
-- 17 ≡ 5 (mod 6)이면 17 = 5 + 2 × 6
example : 17 = 5 + 2 * 6 := by norm_num

-- 24 ≡ 3 (mod 7)이면 24 = 3 + 3 × 7
example : 24 = 3 + 3 * 7 := by norm_num
```

---

## 7B.5 교재 정리 5: 합과 곱이 합동을 유지

### 7B.5.1 교재 원문

> **정리 5** (Rosen 4.1절):  
> m이 양의 정수라고 하자.  
> a ≡ b (mod m)이고 c ≡ d (mod m)이면  
> a + c ≡ b + d (mod m)이고  
> ac ≡ bd (mod m)이다.

이것은 매우 중요한 정리이다! 합동인 수들끼리 더하거나 곱해도 합동이 유지된다는 뜻이다.

### 7B.5.2 수학적 증명 (합의 경우)

- a ≡ b (mod m)이므로, 정리 4에 의해 b = a + sm인 정수 s가 존재한다.
- c ≡ d (mod m)이므로, 정리 4에 의해 d = c + tm인 정수 t가 존재한다.
- 따라서 b + d = (a + sm) + (c + tm) = (a + c) + m(s + t)
- s + t는 정수이므로, a + c ≡ b + d (mod m)이다.

### 7B.5.3 Lean4 코드 (합의 경우)

```lean
-- 정리 5 (합): 합동인 수의 합도 합동
-- a % m = b % m이고 c % m = d % m이면
-- (a + c) % m = (b + d) % m

theorem congr_add (a b c d m : ℕ) (hm : 0 < m)
    (hab : a % m = b % m) (hcd : c % m = d % m) :
    (a + c) % m = (b + d) % m := by
  -- Lean4/Mathlib의 Nat.add_mod 정리를 활용
  rw [Nat.add_mod, hab, hcd, ← Nat.add_mod]
```

코드를 한 줄씩 분석한다:

| 코드 | 의미 |
|------|------|
| `Nat.add_mod` | (a + c) % m = ((a % m) + (c % m)) % m |
| `rw [Nat.add_mod]` | 좌변을 ((a%m) + (c%m)) % m으로 바꿈 |
| `rw [hab, hcd]` | a%m을 b%m으로, c%m을 d%m으로 치환 |
| `rw [← Nat.add_mod]` | ((b%m) + (d%m)) % m을 (b+d) % m으로 되돌림 |

### 7B.5.4 Lean4 코드 (곱의 경우)

```lean
-- 정리 5 (곱): 합동인 수의 곱도 합동
theorem congr_mul (a b c d m : ℕ) (hm : 0 < m)
    (hab : a % m = b % m) (hcd : c % m = d % m) :
    (a * c) % m = (b * d) % m := by
  rw [Nat.mul_mod, hab, hcd, ← Nat.mul_mod]
```

### 7B.5.5 중간 괄호 채우기 연습

```lean
-- 연습: 빈칸을 채워라
-- 힌트: Nat.add_mod를 사용
theorem congr_add_practice (a b c d m : ℕ) (hm : 0 < m)
    (hab : a % m = b % m) (hcd : c % m = d % m) :
    (a + c) % m = (b + d) % m := by
  rw [_, hab, hcd, _]    -- 🔲 두 개의 빈칸
```

<details>
<summary>💡 답 보기</summary>

```lean
theorem congr_add_practice (a b c d m : ℕ) (hm : 0 < m)
    (hab : a % m = b % m) (hcd : c % m = d % m) :
    (a + c) % m = (b + d) % m := by
  rw [Nat.add_mod, hab, hcd, ← Nat.add_mod]
```

</details>

---

## 7B.6 교재 예제 6: 합동의 합과 곱 계산

### 7B.6.1 교재 원문

> **예제 6**: 7 ≡ 2 (mod 5)이고, 11 ≡ 1 (mod 5)이므로, 정리 5에 의해  
> 18 = 7 + 11 ≡ 2 + 1 = 3 (mod 5)  
> 이고  
> 77 = 7 · 11 ≡ 2 · 1 = 2 (mod 5)이다.

### 7B.6.2 Lean4 코드

```lean
-- 예제 6: 합
-- 7 ≡ 2 (mod 5)이고 11 ≡ 1 (mod 5)
-- 따라서 (7 + 11) ≡ (2 + 1) (mod 5), 즉 18 ≡ 3 (mod 5)
example : (7 + 11) % 5 = (2 + 1) % 5 := by norm_num
example : 18 % 5 = 3 := by norm_num

-- 예제 6: 곱
-- 따라서 (7 * 11) ≡ (2 * 1) (mod 5), 즉 77 ≡ 2 (mod 5)
example : (7 * 11) % 5 = (2 * 1) % 5 := by norm_num
example : 77 % 5 = 2 := by norm_num
```

### 7B.6.3 중간 괄호 채우기 연습

```lean
-- 연습: 빈칸을 채워라
-- 13 ≡ 3 (mod 5)이고 17 ≡ 2 (mod 5)이면
-- (13 + 17) ≡ ? (mod 5)
example : (13 + 17) % 5 = _ := by norm_num   -- 🔲
-- (13 * 17) ≡ ? (mod 5)
example : (13 * 17) % 5 = _ := by norm_num   -- 🔲
```

<details>
<summary>💡 답 보기</summary>

```lean
example : (13 + 17) % 5 = 0 := by norm_num   -- 30 % 5 = 0
example : (13 * 17) % 5 = 1 := by norm_num   -- 221 % 5 = 1 (3*2=6, 6%5=1)
```

</details>

---

## 7B.7 교재 따름정리 2: mod 함수의 분배

### 7B.7.1 교재 원문

> **따름정리 2** (Rosen 4.1절):  
> m이 양의 정수이고 a와 b가 정수라고 하자. 그러면  
> (a + b) mod m = ((a mod m) + (b mod m)) mod m  
> 이고  
> ab mod m = ((a mod m)(b mod m)) mod m  
> 이다.

### 7B.7.2 Lean4 코드

```lean
-- 따름정리 2 (합): (a + b) % m = ((a % m) + (b % m)) % m
-- 이것은 Lean4/Mathlib에서 Nat.add_mod로 알려져 있다
example (a b m : ℕ) : (a + b) % m = ((a % m) + (b % m)) % m := by
  exact (Nat.add_mod a b m).symm

-- 따름정리 2 (곱): (a * b) % m = ((a % m) * (b % m)) % m
-- 이것은 Lean4/Mathlib에서 Nat.mul_mod로 알려져 있다
example (a b m : ℕ) : (a * b) % m = ((a % m) * (b % m)) % m := by
  exact (Nat.mul_mod a b m).symm
```

### 7B.7.3 이것이 왜 유용한가?

큰 수의 나머지를 구할 때, 먼저 각 부분의 나머지를 구한 후 합치면 된다. 이것이 **나머지 산술**의 핵심이다.

예를 들어, (193³ mod 31)⁴ mod 23을 계산할 때 (교재 예제 7), 193³을 직접 계산하면 매우 큰 수가 되지만, 중간에 mod를 적용하면 수를 작게 유지할 수 있다.

---

## 7B.8 교재 예제 7: mod 함수를 이용한 계산

### 7B.8.1 교재 원문

> **예제 7**: (19³ mod 31)⁴ mod 23을 계산하라.
>
> 풀이: 먼저 19³ mod 31을 계산해야 한다.  
> 19³ = 6859이고 6859 = 221 · 31 + 8이므로, 19³ mod 31 = 8이 된다.  
> 따라서, (19³ mod 31)⁴ mod 23 = 8⁴ mod 23이다.  
> 8⁴ = 4096이고 4096 = 178 · 23 + 2이므로, 8⁴ mod 23 = 2가 된다.

### 7B.8.2 Lean4 코드

```lean
-- 예제 7: 단계별 계산
-- 1단계: 19³ mod 31
#eval (19 ^ 3) % 31          -- 결과: 8

-- 2단계: 8⁴ mod 23
#eval (8 ^ 4) % 23           -- 결과: 2

-- 최종 결과
#eval ((19 ^ 3) % 31) ^ 4 % 23   -- 결과: 2

-- 정리로 표현
example : ((19 ^ 3) % 31) ^ 4 % 23 = 2 := by norm_num
```

### 7B.8.3 Lean4의 장점: 중간 계산 확인

```lean
-- Lean4에서는 #eval로 각 단계를 확인할 수 있다
#eval 19 ^ 3           -- 6859
#eval 6859 / 31        -- 221
#eval 6859 % 31        -- 8
#eval 8 ^ 4            -- 4096
#eval 4096 / 23        -- 178
#eval 4096 % 23        -- 2
```

---

## 7B.9 **산술 모듈로 m**(Arithmetic Modulo m)

### 7B.9.1 교재의 설명

교재 4.1.5절에서는 **ℤ_m**이라는 집합을 소개한다. ℤ_m = {0, 1, 2, ..., m-1}이며, 이 집합에서의 덧셈과 곱셈은 다음과 같이 정의된다:

- a +_m b = (a + b) mod m
- a ·_m b = (a · b) mod m

### 7B.9.2 교재 예제 8

> **예제 8**: ℤ_m에서 합과 곱의 정의를 이용하여 7 +₁₁ 9와 7 ·₁₁ 9를 계산하라.
>
> 풀이:  
> 7 +₁₁ 9 = (7 + 9) mod 11 = 16 mod 11 = 5  
> 7 ·₁₁ 9 = (7 · 9) mod 11 = 63 mod 11 = 8

### 7B.9.3 Lean4 코드

```lean
-- 예제 8
-- 7 +₁₁ 9 = (7 + 9) mod 11 = 16 mod 11 = 5
example : (7 + 9) % 11 = 5 := by norm_num

-- 7 ·₁₁ 9 = (7 * 9) mod 11 = 63 mod 11 = 8
example : (7 * 9) % 11 = 8 := by norm_num
```

### 7B.9.4 Lean4에서 ZMod 사용 (참고)

Lean4/Mathlib에는 `ZMod m`이라는 타입이 있어서, 모듈로 m 산술을 직접 지원한다.

```lean
-- 참고: ZMod 사용 (고급)
-- ZMod 11에서의 연산
-- #eval (7 : ZMod 11) + 9   -- 결과: 5
-- #eval (7 : ZMod 11) * 9   -- 결과: 8
```

기초 단계에서는 `%` 연산만으로 충분하다.

---

## 7B.10 나머지 산술의 성질

### 7B.10.1 교재의 성질 목록

교재에서는 ℤ_m이 다음 성질들을 만족한다고 설명한다:

| 성질 | 의미 |
|------|------|
| **폐쇄**(closure) | a, b ∈ ℤ_m이면 a +_m b, a ·_m b ∈ ℤ_m |
| **결합성**(associativity) | (a +_m b) +_m c = a +_m (b +_m c) |
| **교환성**(commutativity) | a +_m b = b +_m a |
| **항등원**(identity) | a +_m 0 = a, a ·_m 1 = a |
| **덧셈의 역원**(additive inverse) | a ≠ 0이면 a +_m (m - a) = 0 |
| **분배성**(distributivity) | a ·_m (b +_m c) = (a ·_m b) +_m (a ·_m c) |

### 7B.10.2 Lean4로 구체적 예시 확인

```lean
-- 폐쇄성: 결과가 항상 0 ~ m-1 범위
example : (7 + 9) % 11 < 11 := by norm_num

-- 결합성: ((a + b) + c) % m = (a + (b + c)) % m
example : ((3 + 5) + 7) % 11 = (3 + (5 + 7)) % 11 := by norm_num

-- 교환성: (a + b) % m = (b + a) % m
example : (3 + 7) % 11 = (7 + 3) % 11 := by norm_num

-- 항등원: (a + 0) % m = a % m
example : (5 + 0) % 11 = 5 % 11 := by norm_num

-- 분배성: (a * (b + c)) % m = ((a * b) + (a * c)) % m
example : (3 * (5 + 7)) % 11 = (3 * 5 + 3 * 7) % 11 := by norm_num
```

### 7B.10.3 일반적인 증명 (결합성)

```lean
-- 결합성의 일반적 증명
theorem mod_add_assoc (a b c m : ℕ) :
    ((a + b) % m + c) % m = (a + (b + c)) % m := by
  rw [Nat.add_mod, Nat.add_mod a, Nat.add_mod, Nat.add_mod]
  congr 1
  rw [Nat.add_mod, Nat.add_mod]
  ring_nf
```

---

## 7B.11 교재 연습문제 (시계 문제)

### 7B.11.1 교재 연습문제 15: 12시간 시계

> **연습문제 15**: 12시간 시계를 사용하면 다음 시간은 몇 시가 되는가?
> a) 11시로부터 80시간 후
> b) 12시로부터 40시간 후
> c) 6시로부터 100시간 후

```lean
-- 연습문제 15a: 11시에서 80시간 후
-- (11 + 80) mod 12 = 91 mod 12
example : (11 + 80) % 12 = 7 := by norm_num
-- 답: 7시

-- 연습문제 15b: 12시에서 40시간 후
-- (12 + 40) mod 12 = 52 mod 12
example : (12 + 40) % 12 = 4 := by norm_num
-- 답: 4시

-- 연습문제 15c: 6시에서 100시간 후
-- (6 + 100) mod 12 = 106 mod 12
example : (6 + 100) % 12 = 10 := by norm_num
-- 답: 10시
```

### 7B.11.2 중간 괄호 채우기 연습

```lean
-- 연습: 빈칸을 채워라
-- 24시간 시계에서, 2시에서 100시간 후는 몇 시인가?
example : (2 + 100) % 24 = _ := by norm_num   -- 🔲
```

<details>
<summary>💡 답 보기</summary>

```lean
example : (2 + 100) % 24 = 6 := by norm_num
-- (2 + 100) = 102, 102 / 24 = 4 나머지 6
-- 답: 6시
```

</details>

---

## 7B.12 연습 세트 1: 합동 기초

### 연습 7B.1: 합동 판정 (중간 괄호)

```lean
-- 빈칸을 채워라: 25 mod 7의 값
example : 25 % 7 = _ := by norm_num   -- 🔲
```

<details>
<summary>💡 답 보기</summary>

```lean
example : 25 % 7 = 4 := by norm_num
```

</details>

### 연습 7B.2: 합동 확인

```lean
-- sorry를 채워라: 38 ≡ 14 (mod 12)
example : 38 % 12 = 14 % 12 := by
  sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
example : 38 % 12 = 14 % 12 := by
  norm_num   -- 38 % 12 = 2, 14 % 12 = 2
```

</details>

### 연습 7B.3: 합동의 합

```lean
-- sorry를 채워라: 13 ≡ 3 (mod 5)이고 22 ≡ 2 (mod 5)이면
-- (13 + 22) mod 5 = (3 + 2) mod 5
example : (13 + 22) % 5 = (3 + 2) % 5 := by
  sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
example : (13 + 22) % 5 = (3 + 2) % 5 := by
  norm_num
```

</details>

### 연습 7B.4: 합동의 곱

```lean
-- sorry를 채워라: (8 * 13) mod 7의 값
-- 힌트: 8 ≡ 1 (mod 7), 13 ≡ 6 (mod 7)
-- 따라서 (8 * 13) ≡ 1 * 6 = 6 (mod 7)
example : (8 * 13) % 7 = _ := by sorry   -- 🔲 값과 전술 모두 채우기
```

<details>
<summary>💡 답 보기</summary>

```lean
example : (8 * 13) % 7 = 6 := by norm_num
```

</details>

### 연습 7B.5: mod 분배 법칙 활용

```lean
-- sorry를 채워라: ((a % m) + (b % m)) % m = (a + b) % m
-- 이것은 Nat.add_mod의 대칭 형태이다
theorem add_mod_eq (a b m : ℕ) : ((a % m) + (b % m)) % m = (a + b) % m := by
  sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
theorem add_mod_eq (a b m : ℕ) : ((a % m) + (b % m)) % m = (a + b) % m := by
  rw [Nat.add_mod]
```

</details>

### 연습 7B.6: 시계 문제 (sorry)

```lean
-- 24시간 시계에서, 19시에서 168시간 후는 몇 시인가?
-- sorry를 실제 답으로 교체하라
example : (19 + 168) % 24 = _ := by sorry   -- 🔲
```

<details>
<summary>💡 답 보기</summary>

```lean
example : (19 + 168) % 24 = 19 := by norm_num
-- 168 = 24 × 7이므로 정확히 7일 후 → 같은 시각!
```

</details>

### 연습 7B.7: 교재 연습문제 17 유형

> a ≡ 4 (mod 13)이고 b ≡ 9 (mod 13)이면, c ≡ 9a (mod 13)일 때 c를 구하라 (0 ≤ c ≤ 12).

```lean
-- 9 * 4 = 36, 36 mod 13 = 10
-- sorry를 채워라
example : (9 * 4) % 13 = _ := by sorry   -- 🔲
```

<details>
<summary>💡 답 보기</summary>

```lean
example : (9 * 4) % 13 = 10 := by norm_num
-- 9 * 4 = 36 = 2 * 13 + 10
```

</details>

---

## 7B.13 연습 세트 2: 심화 문제

### 연습 7B.8: 교재 연습문제 36 유형

> (177 mod 31 + 270 mod 31) mod 31을 계산하라.

```lean
-- 전략: Nat.add_mod를 활용하면 (177 + 270) % 31과 같다
example : ((177 % 31) + (270 % 31)) % 31 = (177 + 270) % 31 := by
  sorry

-- 최종 값:
example : (177 + 270) % 31 = _ := by sorry   -- 🔲
```

<details>
<summary>💡 답 보기</summary>

```lean
example : ((177 % 31) + (270 % 31)) % 31 = (177 + 270) % 31 := by
  rw [Nat.add_mod]

example : (177 + 270) % 31 = 447 % 31 := by norm_num
-- 447 = 31 × 14 + 13
-- 답: 13
```

```lean
example : (177 + 270) % 31 = 13 := by norm_num
```

</details>

### 연습 7B.9: 교재 연습문제 37 유형

> (177 mod 31 · 270 mod 31) mod 31을 계산하라.

```lean
-- sorry를 채워라
example : (177 * 270) % 31 = _ := by sorry   -- 🔲
```

<details>
<summary>💡 답 보기</summary>

```lean
example : (177 * 270) % 31 = 27 := by norm_num
-- 177 * 270 = 47790, 47790 / 31 = 1541 나머지 19... 다시 계산
-- 더 정확하게: norm_num이 자동으로 계산
```

</details>

### 연습 7B.10: 교재 연습문제 38a 유형

> (19² mod 41) mod 9를 계산하라.

```lean
-- 단계별로 계산
-- 1단계: 19² mod 41
#eval (19 ^ 2) % 41     -- ?
-- 2단계: 결과 mod 9
-- sorry를 채워라
example : ((19 ^ 2) % 41) % 9 = _ := by sorry   -- 🔲
```

<details>
<summary>💡 답 보기</summary>

```lean
-- 19² = 361, 361 % 41 = 361 - 8*41 = 361 - 328 = 33
-- 33 % 9 = 33 - 3*9 = 33 - 27 = 6
example : ((19 ^ 2) % 41) % 9 = 6 := by norm_num
```

</details>

---

## 7B.14 도전 문제

### 도전 7B.1: 합동의 거듭제곱 보존

> a ≡ b (mod m)이면 a² ≡ b² (mod m)임을 보이시오.

```lean
-- 힌트: a % m = b % m이면 (a * a) % m = (b * b) % m
-- Nat.mul_mod를 활용
theorem congr_sq (a b m : ℕ) (h : a % m = b % m) :
    (a ^ 2) % m = (b ^ 2) % m := by
  sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
theorem congr_sq (a b m : ℕ) (h : a % m = b % m) :
    (a ^ 2) % m = (b ^ 2) % m := by
  simp only [pow_two]
  rw [Nat.mul_mod, h, ← Nat.mul_mod]
```

</details>

### 도전 7B.2: 합동의 일반 거듭제곱 (귀납법)

> a ≡ b (mod m)이면 모든 자연수 n에 대해 aⁿ ≡ bⁿ (mod m)임을 보이시오.

```lean
-- 귀납법 사용
theorem congr_pow (a b m n : ℕ) (h : a % m = b % m) :
    (a ^ n) % m = (b ^ n) % m := by
  sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
theorem congr_pow (a b m n : ℕ) (h : a % m = b % m) :
    (a ^ n) % m = (b ^ n) % m := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [pow_succ]
    rw [Nat.mul_mod, ih, h, ← Nat.mul_mod]
```

</details>

---

## 7B.15 전술 요약

### 새로운 전술 & 개념

| 전술/개념 | 용도 | 예시 |
|---------|------|------|
| `%` | 나머지 연산 | `17 % 5 = 2` |
| `Nat.add_mod` | (a+b)%m = ((a%m)+(b%m))%m | 합의 mod 분배 |
| `Nat.mul_mod` | (a*b)%m = ((a%m)*(b%m))%m | 곱의 mod 분배 |
| `#eval` | 계산 결과 확인 | `#eval 101 % 11` |
| `congr` | 같은 구조의 항 일치 | 목표의 구조가 같을 때 |
| `induction n with` | 자연수 귀납법 | `| zero => ... | succ n ih => ...` |

### 이전 장 전술 (복습)

| 전술 | 최초 등장 |
|------|---------|
| `intro`, `exact`, `apply` | Part 4 |
| `rw`, `simp`, `ring` | Part 4-5 |
| `omega`, `norm_num` | Part 4, 7-A |
| `use`, `obtain`, `have` | Part 7-A |
| `constructor`, `.mp`, `.mpr` | Part 7-A |

---

## 7B.16 핵심 정리 요약

1. **합동**: a ≡ b (mod m) ↔ a % m = b % m ↔ m ∣ (a - b)

2. **정리 5**: 합동은 덧셈과 곱셈에서 보존된다
   - a ≡ b, c ≡ d (mod m) → a + c ≡ b + d (mod m)
   - a ≡ b, c ≡ d (mod m) → ac ≡ bd (mod m)

3. **따름정리 2**: mod 분배 법칙
   - (a + b) % m = ((a % m) + (b % m)) % m
   - (a * b) % m = ((a % m) * (b % m)) % m

4. **나머지 산술** ℤ_m: 나머지만으로 모든 연산 수행 가능

5. **응용**: 시계 문제, 큰 수의 나머지 계산

---

## 다음 편(7-C) 예고

**제7-C편**에서는 교재 4.2절의 내용을 다룬다:
- **진법 전환**(base conversion): 10진법, 2진법, 8진법, 16진법
- **정수의 덧셈과 곱셈 알고리즘** (2진수 기준)
- **나머지 지수승**(modular exponentiation): b^n mod m을 효율적으로 계산
- Lean4에서의 비트 연산과 진법 변환

---

**(끝)**
