# Lean4 Tutorial Part 8-C2: **강 귀납법**(Strong Induction) 연습문제

> **기반 교재**: Kenneth H. Rosen, *Discrete Mathematics and Its Applications* 8판 5.2절  
> **참고 교재**: *Mathematics in Lean* Chapter 5.2, 5.3  
> **선수 지식**: Part 8-A~8-C (수학적 귀납법, 강 귀납법 이론)

---

## 8C2.0 이 파트의 목적

Part 8-C에서 **강 귀납법**(strong induction)의 이론과 핵심 예제(소인수 존재, 우표 문제, 순서화 성질)를 배웠다. 이 파트에서는 Rosen 5.2절의 **연습문제**들을 Lean4로 직접 풀어 보면서 강 귀납법에 완전히 익숙해지는 것이 목표이다.

다루는 내용:

1. **우표 문제 변형** — 3센트 + 5센트, 4센트 + 7센트 등
2. **화폐 문제** — 2달러 + 5달러 조합
3. **√2의 무리수성** — 강 귀납법을 활용한 증명 아이디어
4. **도미노 쓰러뜨리기** — 강 귀납법의 직관적 모델
5. **게임 이론** — Nim 게임 변형에서 이기는 전략
6. **수열 증명** — 강 귀납법으로 부등식, 등식 증명

> 💡 **핵심 복습**: 강 귀납법 vs 보통 귀납법
>
> | | **보통 귀납법** | **강 귀납법** |
> |---|---|---|
> | **가정** | P(k) 하나만 | P(1), P(2), ..., P(k) 전부 |
> | **결론** | P(k+1) | P(k+1) |
> | **Lean4** | `induction n with` | `induction n using Nat.strong_rec_on with` |
> | **언제?** | 바로 이전 값만 필요할 때 | 여러 이전 값이 필요할 때 |

---

## 8C2.1 연습문제 세트 1: 우표 문제 변형 (Rosen 연습 3, 4)

### 이론 복습: 우표 문제란?

**우표 문제**(postage stamp problem)는 "주어진 종류의 우표만으로 특정 금액 이상의 모든 우편 요금을 만들 수 있는가?"라는 문제이다. 이것은 **강 귀납법**의 대표적 응용이다.

Part 8-C에서 배운 핵심 아이디어:

- 4센트 + 5센트 우표로 12센트 이상을 만들 수 있다
- 기본 단계: 여러 개의 초기값을 직접 확인
- 귀납 단계: "k센트를 만들 수 있으면 k+1센트도 만들 수 있다"에서, **이전의 여러 값**을 사용

### 연습 1-1: 3센트 + 5센트 우표 (Rosen 연습 3)

**문제**: 3센트와 5센트 우표만으로 $n$센트의 우표를 만들 수 있다는 명제를 $P(n)$이라 하자. $n ≥ 8$일 때 $P(n)$이 참임을 보여라.

먼저 기본 단계를 확인하자:

- $P(8)$: 8 = 3 + 5 ✓
- $P(9)$: 9 = 3 + 3 + 3 ✓
- $P(10)$: 10 = 5 + 5 ✓

귀납 단계: $k ≥ 10$일 때 $P(j)$가 $8 ≤ j ≤ k$인 모든 $j$에 대해 참이라 가정하자. $P(k+1)$을 보이려면:

- $k + 1 ≥ 11$이므로 $k + 1 - 3 ≥ 8$이다
- 귀납 가정에 의해 $P(k - 2)$가 참이다 (즉 $k-2$센트를 만들 수 있다)
- 여기에 3센트 우표 하나를 더하면 $k+1$센트를 만들 수 있다!

Lean4로 이것을 모델링해 보자:

```lean
-- 3센트와 5센트로 n센트를 만들 수 있는가?
def canMakePostage35 : Nat → Bool
  | 0 => true     -- 0센트는 우표 없이
  | 1 => false
  | 2 => false
  | 3 => true     -- 3
  | 4 => false
  | 5 => true     -- 5
  | 6 => true     -- 3+3
  | 7 => false
  | n + 8 => true -- 8 이상은 항상 가능

-- 기본 단계 확인
example : canMakePostage35 8  = true := by native_decide
example : canMakePostage35 9  = true := by native_decide
example : canMakePostage35 10 = true := by native_decide

-- n ≥ 8이면 canMakePostage35 n = true
theorem canMakePostage35_ge8 (n : Nat) (h : n ≥ 8) :
    canMakePostage35 n = true := by
  -- n = n' + 8 형태로 변환
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  simp [canMakePostage35]
```

> 💡 **왜 `native_decide`를 쓰는가?**
>
> `native_decide`는 Lean4에게 "이걸 직접 계산해 봐"라고 말하는 것이다. `canMakePostage35 8`은 정의에 의해 `true`이므로 계산만 하면 증명이 된다.

### 연습 1-2: 구체적 금액 분해 (괄호 채우기)

각 금액이 3센트와 5센트의 조합으로 표현됨을 보이시오.

```lean
-- a개의 3센트 + b개의 5센트 = n센트
-- 즉 3*a + 5*b = n을 만족하는 (a, b) 찾기

-- P(8): 8 = 3×1 + 5×1
example : 3 * 1 + 5 * (______) = 8 := by norm_num

-- P(9): 9 = 3×3 + 5×0
example : 3 * (______) + 5 * 0 = 9 := by norm_num

-- P(11): 11 = 3×2 + 5×1
example : 3 * 2 + 5 * (______) = 11 := by norm_num

-- P(14): 14 = 3×3 + 5×1
example : 3 * (______) + 5 * (______) = 14 := by norm_num
```

<details>
<summary>💡 답 보기</summary>

```lean
example : 3 * 1 + 5 * 1 = 8 := by norm_num
example : 3 * 3 + 5 * 0 = 9 := by norm_num
example : 3 * 2 + 5 * 1 = 11 := by norm_num
example : 3 * 3 + 5 * 1 = 14 := by norm_num
```

**설명**: `norm_num`은 수치 계산을 자동으로 해주는 전술이다. 예를 들어 `3 * 3 + 5 * 1 = 9 + 5 = 14`를 자동 검증한다.

</details>

---

### 연습 1-3: 4센트 + 7센트 우표 (Rosen 연습 4)

**문제**: 4센트와 7센트 우표만으로 $n$센트의 우표를 만들 수 있다는 명제를 $P(n)$이라 하자. $n ≥ 18$일 때 $P(n)$이 참이다.

#### (a) 기본 단계 확인 (괄호 채우기)

```lean
-- P(18): 18 = 4×1 + 7×2
example : 4 * 1 + 7 * 2 = (______) := by norm_num

-- P(19): 19 = 4×3 + 7×1
example : 4 * (______) + 7 * (______) = 19 := by norm_num

-- P(20): 20 = 4×5 + 7×0
example : 4 * (______) + 7 * 0 = 20 := by norm_num

-- P(21): 21 = 4×0 + 7×3
example : 4 * 0 + 7 * (______) = 21 := by norm_num
```

<details>
<summary>💡 답 보기</summary>

```lean
example : 4 * 1 + 7 * 2 = 18 := by norm_num
example : 4 * 3 + 7 * 1 = 19 := by norm_num
example : 4 * 5 + 7 * 0 = 20 := by norm_num
example : 4 * 0 + 7 * 3 = 21 := by norm_num
```

**설명**: 기본 단계에서 P(18), P(19), P(20), P(21)의 4개를 확인한다. 왜 4개인가? 4센트 우표를 하나 추가하면 4센트가 늘어나므로, 연속 4개의 시작점이 필요하다.

</details>

#### (b) 귀납적 가정은 무엇인가?

> 강 귀납법의 귀납적 가정은 "$k ≥ 21$인 정수일 때 $18 ≤ j ≤ k$인 모든 $j$에 대해 $P(j)$가 참이다"이다.

#### (c) 귀납 단계 (sorry 채우기)

$k ≥ 21$일 때 $P(k+1)$을 보이려면:

- $k + 1 ≥ 22$이므로 $k + 1 - 4 = k - 3 ≥ 18$
- 귀납 가정에 의해 $P(k - 3)$이 참, 즉 $k - 3$센트를 만들 수 있다
- 4센트 우표 하나를 더하면 $k + 1$센트!

```lean
-- k-3 센트를 만들 수 있으면, 4센트를 더해 k+1 센트를 만든다
-- 이것은 (k-3) + 4 = k+1이므로 성립
example : ∀ k : Nat, k ≥ 3 → (k - 3) + 4 = k + 1 := by
  sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
example : ∀ k : Nat, k ≥ 3 → (k - 3) + 4 = k + 1 := by
  intro k hk
  omega
```

**설명**: `omega`는 자연수의 선형 산술을 자동으로 처리한다. $k ≥ 3$이면 $(k - 3) + 4 = k + 1$은 자명하다.

</details>

---

### 연습 1-4: 왜 이 과정이 $n ≥ 18$일 때 참을 보이는가? (Rosen 연습 4e)

> $n < 18$에서는 만들 수 없는 금액이 존재한다. 예를 들어:
> - 1, 2, 3, 5, 6, 9, 10, 13, 17센트는 4센트 + 7센트로 만들 수 없다
> - 하지만 $n ≥ 18$이면 연속 4개(18, 19, 20, 21)가 모두 가능하므로, 이후 4를 더해가면 모두 가능하다

```lean
-- 만들 수 없는 금액 예시
example : ¬ ∃ a b : Nat, 4 * a + 7 * b = 1  := by omega
example : ¬ ∃ a b : Nat, 4 * a + 7 * b = 2  := by omega
example : ¬ ∃ a b : Nat, 4 * a + 7 * b = 3  := by omega
example : ¬ ∃ a b : Nat, 4 * a + 7 * b = 17 := by omega

-- 연습: 다음 중 만들 수 없는 금액을 찾으시오 (sorry를 true/false로 채우기)
-- 만들 수 있으면 ∃ a b, 4*a + 7*b = n을 보이고
-- 만들 수 없으면 ¬ ∃ a b, 4*a + 7*b = n을 보이시오

-- 5센트: 만들 수 없다
example : ¬ ∃ a b : Nat, 4 * a + 7 * b = 5 := by sorry

-- 11센트: 만들 수 있다 (4×1 + 7×1)
example : ∃ a b : Nat, 4 * a + 7 * b = 11 := by sorry

-- 15센트: 만들 수 있다 (4×2 + 7×1)
example : ∃ a b : Nat, 4 * a + 7 * b = 15 := by sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
example : ¬ ∃ a b : Nat, 4 * a + 7 * b = 5 := by omega

example : ∃ a b : Nat, 4 * a + 7 * b = 11 := ⟨1, 1, by norm_num⟩

example : ∃ a b : Nat, 4 * a + 7 * b = 15 := ⟨2, 1, by norm_num⟩
```

**설명**:
- `omega`는 자연수 선형 부등식을 자동 판별한다. 해가 없으면 `¬ ∃`를 증명한다.
- `⟨1, 1, by norm_num⟩`은 증인(witness)을 직접 제시하는 방법이다: "a=1, b=1이면 4×1 + 7×1 = 11"

</details>

---

## 8C2.2 연습문제 세트 2: 화폐 문제 (Rosen 연습 7, 8)

### 연습 2-1: 2달러 + 5달러 지폐 (Rosen 연습 7)

**문제**: 2달러와 5달러 지폐만을 가지고 얼마의 돈을 만들 수 있는가?

먼저 규칙을 발견해 보자:

| 금액 | 가능? | 분해 |
|------|-------|------|
| 1 | ✗ | |
| 2 | ✓ | 2 |
| 3 | ✗ | |
| 4 | ✓ | 2+2 |
| 5 | ✓ | 5 |
| 6 | ✓ | 2+2+2 |
| 7 | ✓ | 2+5 |
| 8 | ✓ | 2+2+2+2 |

**패턴**: 1달러와 3달러를 제외한 **4 이상의 모든 정수**를 만들 수 있다!

```lean
-- 2달러 + 5달러로 만들 수 있는 금액
-- n ≥ 4이면 항상 가능함을 확인

-- 기본 단계
example : ∃ a b : Nat, 2 * a + 5 * b = 4 := ⟨2, 0, by norm_num⟩
example : ∃ a b : Nat, 2 * a + 5 * b = 5 := ⟨0, 1, by norm_num⟩

-- 연습: 6~10을 분해하시오 (sorry 채우기)
example : ∃ a b : Nat, 2 * a + 5 * b = 6 := by sorry
example : ∃ a b : Nat, 2 * a + 5 * b = 7 := by sorry
example : ∃ a b : Nat, 2 * a + 5 * b = 8 := by sorry
example : ∃ a b : Nat, 2 * a + 5 * b = 9 := by sorry
example : ∃ a b : Nat, 2 * a + 5 * b = 10 := by sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
example : ∃ a b : Nat, 2 * a + 5 * b = 6  := ⟨3, 0, by norm_num⟩
example : ∃ a b : Nat, 2 * a + 5 * b = 7  := ⟨1, 1, by norm_num⟩
example : ∃ a b : Nat, 2 * a + 5 * b = 8  := ⟨4, 0, by norm_num⟩
example : ∃ a b : Nat, 2 * a + 5 * b = 9  := ⟨2, 1, by norm_num⟩
example : ∃ a b : Nat, 2 * a + 5 * b = 10 := ⟨0, 2, by norm_num⟩
```

**귀납적 아이디어**: $n ≥ 4$일 때 $P(n)$을 보이려면:
- 기본: P(4) = 2+2, P(5) = 5
- 귀납: $P(k)$가 참이면 $P(k+2)$도 참 (2달러 하나 추가)

이것은 보통 귀납법만으로도 가능하지만, 기본 단계가 2개(짝수, 홀수)이므로 **강 귀납법**의 특수한 형태이다.

</details>

---

### 연습 2-2: 상품권 문제 (Rosen 연습 8)

**문제**: 25달러와 40달러짜리 상품권이 있다. 이 상품권을 사용하여 만들 수 있는 금액은 얼마인지 결정하고 강 귀납법으로 답을 증명하라.

```lean
-- 25와 40의 최대공약수
#eval Nat.gcd 25 40  -- 5

-- 따라서 5의 배수만 만들 수 있다
-- 더 정확히는: 25a + 40b 형태의 수 = 5(5a + 8b)
-- 5센트 + 8센트 문제로 귀결!

-- 확인: 다음 금액을 만들 수 있는가?
-- 100 = 25×4
example : ∃ a b : Nat, 25 * a + 40 * b = 100 := ⟨4, 0, by norm_num⟩

-- 200 = 25×0 + 40×5
example : ∃ a b : Nat, 25 * a + 40 * b = 200 := ⟨0, 5, by norm_num⟩

-- 연습: 150달러를 만들 수 있는가? (sorry 채우기)
example : ∃ a b : Nat, 25 * a + 40 * b = 150 := by sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
-- 150 = 25×2 + 40×( ?)  → 150 - 50 = 100 = 40×2 + 20... 안 됨
-- 150 = 25×6 + 40×0  → 맞다!
example : ∃ a b : Nat, 25 * a + 40 * b = 150 := ⟨6, 0, by norm_num⟩
```

</details>

---

## 8C2.3 연습문제 세트 3: 소인수 존재와 산술의 기본 정리 (Rosen 예제 2)

### 이론 복습: 산술의 기본 정리

**산술의 기본 정리**(fundamental theorem of arithmetic)는 "1보다 큰 모든 양의 정수는 소수들의 곱으로 유일하게 나타낼 수 있다"는 것이다. 이것의 **존재** 부분을 강 귀납법으로 증명한다.

**증명 아이디어** (Part 8-C에서 학습):

- 기본 단계: $P(2)$는 참 (2는 그 자체가 소수)
- 귀납 단계: $2 ≤ j ≤ k$인 모든 $j$에 대해 $P(j)$가 참이라 가정
  - $k+1$이 소수이면 끝
  - $k+1$이 합성수이면 $k+1 = a × b$ ($2 ≤ a ≤ b < k+1$)
  - 귀납 가정에 의해 $a$와 $b$는 소수들의 곱 → $k+1$도 소수들의 곱

### 연습 3-1: Lean4로 소인수분해 확인 (괄호 채우기)

```lean
import Mathlib.Data.Nat.Factors

-- Lean4의 소인수분해 함수
#eval Nat.primeFactorsList 12    -- [2, 2, 3]
#eval Nat.primeFactorsList 100   -- [2, 2, 5, 5]
#eval Nat.primeFactorsList 2024  -- [2, 2, 2, 11, 23]

-- 연습: 다음 수의 소인수분해를 예측하고 확인하시오
-- 360 = 2³ × 3² × 5 = [2, 2, 2, 3, 3, 5]
#eval Nat.primeFactorsList 360
-- 예측이 맞는지 확인:
example : Nat.primeFactorsList 360 = [2, 2, 2, 3, 3, (______)] := by native_decide
```

<details>
<summary>💡 답 보기</summary>

```lean
example : Nat.primeFactorsList 360 = [2, 2, 2, 3, 3, 5] := by native_decide
```

</details>

### 연습 3-2: 소수 판별과 강 귀납법 (sorry 채우기)

```lean
import Mathlib.Data.Nat.Prime.Basic

-- 2 이상의 자연수는 소인수를 갖는다 (Mathematics in Lean의 핵심 정리)
-- 이것이 강 귀납법의 대표적 활용이다

-- 구체적 사례 확인
-- 6은 소인수 2를 갖는다
example : ∃ p : Nat, p.Prime ∧ p ∣ 6 := by sorry

-- 15는 소인수 3을 갖는다
example : ∃ p : Nat, p.Prime ∧ p ∣ 15 := by sorry

-- 101은 소수이다 (자기 자신이 소인수)
example : Nat.Prime 101 := by sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
-- 6 = 2 × 3이므로 2가 소인수
example : ∃ p : Nat, p.Prime ∧ p ∣ 6 := ⟨2, by norm_num, ⟨3, by norm_num⟩⟩

-- 15 = 3 × 5이므로 3이 소인수
example : ∃ p : Nat, p.Prime ∧ p ∣ 15 := ⟨3, by norm_num, ⟨5, by norm_num⟩⟩

-- 101은 소수
example : Nat.Prime 101 := by norm_num
```

**설명**:
- `⟨2, by norm_num, ⟨3, by norm_num⟩⟩`는 "p = 2이고, 2는 소수이고(`by norm_num`이 확인), 2가 6을 나눈다(몫이 3)"를 의미한다.
- `by norm_num`은 소수 판별과 수치 계산을 자동으로 수행한다.

</details>

---

## 8C2.4 연습문제 세트 4: 강 귀납법으로 수열 부등식 증명

### 이론: 피보나치 수와 강 귀납법

**피보나치 수열**(Fibonacci sequence)은 강 귀납법이 가장 자연스럽게 필요한 예이다. $f_n = f_{n-1} + f_{n-2}$이므로 바로 이전 값 $f_{n-1}$뿐 아니라 그 전 값 $f_{n-2}$도 필요하기 때문이다.

### 연습 4-1: 피보나치 수 계산 확인 (괄호 채우기)

```lean
-- Lean4에서 피보나치 수 직접 정의
def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

-- 계산 확인
#eval fib 0   -- 0
#eval fib 1   -- 1
#eval fib 5   -- 5
#eval fib 10  -- 55

-- 연습: 빈칸 채우기
example : fib 6 = (______) := by native_decide
example : fib 7 = (______) := by native_decide
example : fib 8 = (______) := by native_decide
```

<details>
<summary>💡 답 보기</summary>

```lean
example : fib 6 = 8  := by native_decide
example : fib 7 = 13 := by native_decide
example : fib 8 = 21 := by native_decide
```

**계산 과정**:
- fib 6 = fib 4 + fib 5 = 3 + 5 = 8
- fib 7 = fib 5 + fib 6 = 5 + 8 = 13
- fib 8 = fib 6 + fib 7 = 8 + 13 = 21

</details>

### 연습 4-2: 피보나치 수열의 증가성 (괄호 채우기)

$n ≥ 1$일 때 $f_n ≤ f_{n+1}$임을 구체적으로 확인하자.

```lean
-- fib n ≤ fib (n + 1)의 구체적 사례
example : fib 1 ≤ fib 2 := by (______)
example : fib 5 ≤ fib 6 := by (______)
example : fib 10 ≤ fib 11 := by (______)
```

<details>
<summary>💡 답 보기</summary>

```lean
example : fib 1 ≤ fib 2 := by native_decide
example : fib 5 ≤ fib 6 := by native_decide
example : fib 10 ≤ fib 11 := by native_decide
```

**설명**: `native_decide`가 `fib 5 = 5 ≤ 8 = fib 6`을 직접 계산하여 확인한다.

</details>

### 연습 4-3: 피보나치 제곱합 (Rosen 5.3절 관련)

$f_1^2 + f_2^2 + \cdots + f_n^2 = f_n \cdot f_{n+1}$

이 등식을 구체적으로 확인하자:

```lean
-- n = 1: f₁² = 1 = f₁ × f₂ = 1 × 1
example : fib 1 ^ 2 = fib 1 * fib 2 := by native_decide

-- n = 4: f₁² + f₂² + f₃² + f₄² = 1+1+4+9 = 15 = 3×5 = f₄ × f₅
example : fib 1 ^ 2 + fib 2 ^ 2 + fib 3 ^ 2 + fib 4 ^ 2
    = fib 4 * fib 5 := by native_decide

-- 연습: n = 6 확인 (sorry 채우기)
example : fib 1 ^ 2 + fib 2 ^ 2 + fib 3 ^ 2 + fib 4 ^ 2 +
          fib 5 ^ 2 + fib 6 ^ 2
    = fib 6 * fib 7 := by sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
example : fib 1 ^ 2 + fib 2 ^ 2 + fib 3 ^ 2 + fib 4 ^ 2 +
          fib 5 ^ 2 + fib 6 ^ 2
    = fib 6 * fib 7 := by native_decide
```

**확인**: $1 + 1 + 4 + 9 + 25 + 64 = 104 = 8 × 13$ ✓

</details>

---

## 8C2.5 연습문제 세트 5: 강 귀납법의 구조 연습

### 연습 5-1: "모든 양의 정수는 2의 거듭제곱들의 합으로 쓸 수 있다" (Rosen 연습 12)

이것은 **이진 표현**(binary representation)이 존재한다는 것과 같다. 강 귀납법으로 증명한다.

**증명 아이디어**:
- 기본: $P(1)$은 참 ($1 = 2^0$)
- 귀납: $1 ≤ j ≤ k$인 모든 $j$에 대해 $P(j)$가 참이라 가정
  - $k+1$이 짝수이면: $k+1 = 2m$, $m ≤ k$이므로 귀납 가정에 의해 $m$은 2의 거듭제곱의 합 → 각 항에 2를 곱하면 $k+1$도
  - $k+1$이 홀수이면: $k+1 = 2m + 1$, $2m$은 위와 같이 처리하고 $2^0 = 1$을 더한다

```lean
-- 이진 표현의 존재를 구체적으로 확인
-- 13 = 8 + 4 + 1 = 2³ + 2² + 2⁰
example : 13 = 2^3 + 2^2 + 2^0 := by norm_num

-- 연습: 다음 수의 이진 표현을 찾으시오 (sorry 채우기)
-- 25 = ?
example : 25 = 2^4 + 2^3 + 2^0 := by sorry

-- 42 = ?
example : 42 = 2^5 + 2^3 + 2^1 := by sorry

-- 100 = ?
example : 100 = 2^6 + 2^5 + 2^2 := by sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
-- 25 = 16 + 8 + 1
example : 25 = 2^4 + 2^3 + 2^0 := by norm_num

-- 42 = 32 + 8 + 2
example : 42 = 2^5 + 2^3 + 2^1 := by norm_num

-- 100 = 64 + 32 + 4
example : 100 = 2^6 + 2^5 + 2^2 := by norm_num
```

</details>

### 연습 5-2: 잘못된 "증명" 찾기 (Rosen 연습 29)

다음 강 귀납법에 의한 "증명"에서 잘못된 것은?

> "정리": 모든 음이 아닌 정수 $n$에 대해서, $5n = 0$이다.
>
> 기본 단계: $5 \cdot 0 = 0$ ✓
>
> 귀납적 단계: $0 ≤ j ≤ k$인 모든 정수 $j$에 대해 $5j = 0$이라 가정하자. $k + 1$보다 작은 자연수 $i, j$에 대해 $k + 1 = i + j$라 쓰자. 귀납적 가설에 의해 $5(k + 1) = 5(i + j) = 5i + 5j = 0 + 0 = 0$이다.

```lean
-- 이 "증명"은 틀렸다! 왜?
-- k = 0일 때, k + 1 = 1인데
-- 1 = i + j (i, j < 1)를 만족하는 자연수 i, j가 존재하지 않는다!
-- 즉, i = j = 0이면 i + j = 0 ≠ 1

-- 핵심: 귀납 단계에서 k = 0인 경우를 처리하지 못했다
-- 이것은 강 귀납법에서 "귀납 가정을 실제로 사용할 수 없는 경우"가
-- 기본 단계로 처리되어야 하는데, 이것을 빠뜨린 것이다

-- 반례: 5 × 1 ≠ 0
example : 5 * 1 ≠ 0 := by norm_num
```

> 💡 **교훈**: 강 귀납법에서도 귀납 단계가 실제로 적용될 수 있는지 확인해야 한다. 귀납 가정에서 필요한 값이 기본 범위 안에 있는지 반드시 확인하라!

---

## 8C2.6 연습문제 세트 6: 순서화 성질 활용 (Rosen 연습 36, 37)

### 이론 복습: 순서화 성질

**순서화 성질**(well-ordering property): 음이 아닌 정수들의 공집합이 아닌 모든 집합은 **가장 작은 원소**를 갖는다.

이것은 강 귀납법과 **동치**이다! (Rosen 연습 41, 42, 43)

### 연습 6-1: 나눗셈 알고리즘의 존재성 (Rosen 예제 5 / 연습 37)

나눗셈 알고리즘은 $a$가 정수이고 $d$가 양의 정수일 때, $a = dq + r$ ($0 ≤ r < d$)인 유일한 $q$와 $r$이 존재한다는 것이다.

순서화 성질을 사용한 존재성 증명:

```lean
-- Lean4에서 나눗셈과 나머지
-- a / d = 몫, a % d = 나머지

-- 기본 성질: a = d * (a / d) + a % d
example (a d : Nat) (hd : d > 0) : a = d * (a / d) + a % d := by
  exact (Nat.div_add_mod a d).symm

-- 나머지는 항상 d보다 작다
example (a d : Nat) (hd : d > 0) : a % d < d := by
  exact Nat.mod_lt a hd

-- 연습: 구체적 사례 확인 (괄호 채우기)
-- 17 = 5 × 3 + 2
example : 17 / 5 = (______) := by norm_num
example : 17 % 5 = (______) := by norm_num
example : 5 * (17 / 5) + 17 % 5 = (______) := by norm_num
```

<details>
<summary>💡 답 보기</summary>

```lean
example : 17 / 5 = 3 := by norm_num
example : 17 % 5 = 2 := by norm_num
example : 5 * (17 / 5) + 17 % 5 = 17 := by norm_num
```

</details>

---

## 8C2.7 종합 도전 문제

### 도전 1: Nim 게임 변형 (Rosen 연습 11 관련)

**Nim 게임**: $n$개의 성냥을 가지고 시작한다. 두 사람이 교대로 한 번에 1, 2, 또는 3개의 성냥을 제거한다. 마지막 성냥을 제거하는 사람이 진다.

```lean
-- 4의 배수일 때 첫 번째 사람이 이긴다
-- 전략: 상대가 k개를 제거하면 나는 4-k개를 제거

-- isWinForFirst n = true: 선수 필승
-- 패턴: n ≡ 0 (mod 4)이면 후수 필승, 아니면 선수 필승
-- (마지막을 가져가면 지는 규칙)
def isLoseForFirst : Nat → Bool
  | n => n % 4 == 0

-- 확인
example : isLoseForFirst 4  = true  := by native_decide
example : isLoseForFirst 8  = true  := by native_decide
example : isLoseForFirst 1  = false := by native_decide
example : isLoseForFirst 5  = false := by native_decide

-- 연습: 다음 경우 누가 이기는가? (sorry 채우기)
example : isLoseForFirst 12 = true  := by sorry  -- 12는 4의 배수
example : isLoseForFirst 7  = false := by sorry  -- 7은 4의 배수 아님
```

<details>
<summary>💡 답 보기</summary>

```lean
example : isLoseForFirst 12 = true  := by native_decide
example : isLoseForFirst 7  = false := by native_decide
```

**전략 설명**:
- $n = 4k$일 때: 첫 번째 사람이 무엇을 하든($i$개 제거, $1 ≤ i ≤ 3$), 두 번째 사람이 $4 - i$개를 제거하면 다시 $4(k-1)$개가 남는다. 이것을 반복하면 결국 $4$개가 남고, 첫 번째 사람이 마지막 1개를 가져가게 된다.
- $n ≠ 4k$일 때: 첫 번째 사람이 $n \mod 4$개를 제거하면 $4k$개가 남아 상대가 불리해진다.

</details>

### 도전 2: n개의 돌 나누기 (Rosen 연습 14)

**문제**: $n$개의 돌로 이루어진 더미가 있다. 이것을 계속 작은 더 개로 나누어 하나의 돌로 이루어진 $n$개의 더미로 만든다. 매번 더미를 나눌 때 만들어진 작은 두 더미의 돌의 수를 곱한다. 어떻게 더미를 나누든 간에 각 단계에서 곱해서 얻은 수에 대한 합은 $n(n − 1)/2$임을 보여라.

```lean
-- 예시: n = 4
-- 방법 1: 4 → (2,2) → (1,1)(1,1)
--   곱: 2×2 + 1×1 + 1×1 = 4 + 1 + 1 = 6 = 4×3/2 ✓
-- 방법 2: 4 → (1,3) → (1)(1,2) → (1)(1)(1,1)
--   곱: 1×3 + 1×2 + 1×1 = 3 + 2 + 1 = 6 = 4×3/2 ✓

-- 구체적 확인
example : 4 * 3 / 2 = 6 := by norm_num
example : 5 * 4 / 2 = 10 := by norm_num

-- 연습: n = 5의 한 가지 분해를 찾고 합을 확인하시오
-- 5 → (2, 3) → (1,1)(1,2) → (1,1)(1)(1,1)
-- 곱: 2×3 + 1×1 + 1×2 + 1×1 = 6 + 1 + 2 + 1 = 10
example : 2*3 + 1*1 + 1*2 + 1*1 = 5 * 4 / 2 := by sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
example : 2*3 + 1*1 + 1*2 + 1*1 = 5 * 4 / 2 := by norm_num
```

**왜 항상 같은 값이 나오는가?** (강 귀납법 증명 아이디어)

$P(n)$을 "n개의 돌 더미를 나누면 곱의 합이 항상 $n(n-1)/2$"라 하자.

- 기본: $P(1)$은 참 (나눌 필요 없고, 합 = 0 = 1×0/2)
- 귀납: $n$개의 돌을 $r$개와 $n-r$개로 나누면 ($1 ≤ r < n$):
  - 첫 곱: $r × (n - r)$
  - $r$개 더미의 곱 합: $r(r-1)/2$ (귀납 가정)
  - $(n-r)$개 더미의 곱 합: $(n-r)(n-r-1)/2$ (귀납 가정)
  - 총합: $r(n-r) + r(r-1)/2 + (n-r)(n-r-1)/2 = n(n-1)/2$ ✓

</details>

---

## 8C2.8 전술 요약

### 이 파트에서 사용한 주요 전술

| 전술 | 용도 | 사용 예 |
|------|------|--------|
| `native_decide` | 구체적 계산 검증 | `fib 10 = 55` 확인 |
| `norm_num` | 수치 계산 자동화 | `3 * 3 + 5 * 1 = 14` |
| `omega` | 자연수 선형 산술 | 부등식 증명, 불가능성 |
| `⟨a, b, proof⟩` | 존재 증인 제시 | `∃ a b, 4*a + 7*b = 11` |
| `by norm_num` | `⟨⟩` 안의 계산 증명 | 수치 조건 확인 |

### 강 귀납법 핵심 정리

1. **강 귀납법**은 귀납 가정에서 $P(1), P(2), \ldots, P(k)$ **모두**를 사용할 수 있다
2. **우표 문제**: 기본 단계를 **여러 개** 확인하고, 이전 값(보통 $k - c$)을 사용
3. **소인수 존재**: 합성수 $n = ab$에서 $a, b < n$이므로 귀납 가정 적용
4. **순서화 성질**: "공집합이 아닌 자연수 집합은 최솟값을 가진다" ↔ 강 귀납법
5. **잘못된 증명 찾기**: 귀납 단계가 실제로 적용되는 범위를 확인!

---

## 다음 편(8-E) 예고

다음 편에서는:
- **구조적 귀납법**(structural induction)
- **이진 트리**(binary tree)의 재귀적 정의
- **포화 이진 트리**의 꼭짓점 수 정리
- Lean4에서 `inductive` 타입에 대한 귀납 증명

을 다룬다.

---

**(끝)**
