# Lean4 Tutorial Part 4-5: 증명 방법과 전략

> **기반 교재**: Kenneth H. Rosen, *Discrete Mathematics and Its Applications* 8판, 1.8절
> **선수 지식**: Part 4-4 (추론 규칙과 증명의 소개)

---

## 목차

- [4-5.1 서론: 증명 전략의 확장](#4-51-서론-증명-전략의-확장)
- [4-5.2 전수 증명과 경우에 의한 증명](#4-52-전수-증명과-경우에-의한-증명)
- [4-5.3 Lean4에서 전수 증명 구현](#4-53-lean4에서-전수-증명-구현)
- [4-5.4 경우에 의한 증명의 원리](#4-54-경우에-의한-증명의-원리)
- [4-5.5 Lean4에서 경우에 의한 증명](#4-55-lean4에서-경우에-의한-증명)
- [4-5.6 일반성을 잃지 않고(WLOG)](#4-56-일반성을-잃지-않고wlog)
- [4-5.7 존재 증명: 생산적 증명과 비생산적 증명](#4-57-존재-증명-생산적-증명과-비생산적-증명)
- [4-5.8 Lean4에서 존재 증명](#4-58-lean4에서-존재-증명)
- [4-5.9 유일성 증명](#4-59-유일성-증명)
- [4-5.10 Lean4에서 유일성 증명](#4-510-lean4에서-유일성-증명)
- [4-5.11 증명 전략: 전향 추론과 후향 추론](#4-511-증명-전략-전향-추론과-후향-추론)
- [4-5.12 반례 찾기](#4-512-반례-찾기)
- [4-5.13 Lean4에서 반례 표현](#4-513-lean4에서-반례-표현)
- [4-5.14 종합 연습문제](#4-514-종합-연습문제)
- [4-5.15 도전 문제](#4-515-도전-문제)
- [4-5.16 요약](#4-516-요약)
- [부록: 증명 방법 Lean4 전술 총정리](#부록-증명-방법-lean4-전술-총정리)

---

## 4-5.1 서론: 증명 전략의 확장

### 학습 목표

Part 4-4에서 우리는 직접 증명, 대우에 의한 증명, 모순에 의한 증명의 기초를 배웠다. 이 장에서는 이러한 기본 방법들을 확장하여 더 다양한 증명 전략을 학습한다.

### 이번 장에서 배울 내용

| 증명 방법 | 설명 | Lean4 핵심 전술 |
|--------|------|-------------|
| **전수 증명**(exhaustive proof) | 모든 가능한 경우를 직접 검사 | `decide`, `native_decide` |
| **경우에 의한 증명**(proof by cases) | 경우를 나누어 각각 증명 | `cases`, `rcases`, `match` |
| **존재 증명**(existence proof) | 조건을 만족하는 원소의 존재 | `use`, `obtain` |
| **유일성 증명**(uniqueness proof) | 단 하나만 존재함을 증명 | `∃!`, `use`, `intro` |
| **반례**(counterexample) | 거짓임을 보이기 위한 예시 | 구체적 값 제시 |

### 추론 규칙 복습

**경우에 의한 증명**의 핵심 추론 규칙:

$$[(p_1 \vee p_2 \vee \cdots \vee p_n) \rightarrow q] \leftrightarrow [(p_1 \rightarrow q) \wedge (p_2 \rightarrow q) \wedge \cdots \wedge (p_n \rightarrow q)]$$

이 규칙은 "여러 명제의 논리합으로 구성된 가정을 갖는 조건문은 각각 개별적으로 $p_i \rightarrow q$를 보임으로써 증명할 수 있다"는 것이다.

---

## 4-5.2 전수 증명과 경우에 의한 증명

### 전수 증명이란?

**전수 증명**(exhaustive proof)은 모든 가능한 경우를 빠짐없이 조사하여 정리를 증명하는 방법이다. 가능한 경우의 수가 비교적 적을 때 사용할 수 있다.

### 예제 1 (Rosen 1.8절 예제 1)

**문제**: $n$이 $n \leq 4$인 양의 정수이면 $(n + 1)^3 \geq 3n$임을 증명하라.

**풀이**: $n = 1, 2, 3, 4$일 때 각각 검사한다.

| $n$ | $(n+1)^3$ | $3n$ | $(n+1)^3 \geq 3n$? |
|-----|-----------|------|-------------------|
| 1 | $2^3 = 8$ | 3 | $8 \geq 3$ ✓ |
| 2 | $3^3 = 27$ | 6 | $27 \geq 6$ ✓ |
| 3 | $4^3 = 64$ | 9 | $64 \geq 9$ ✓ |
| 4 | $5^3 = 125$ | 12 | $125 \geq 12$ ✓ |

모든 경우에서 성립하므로 정리가 증명되었다.

### 경우에 의한 증명이란?

**경우에 의한 증명**(proof by cases)은 정리에 나오는 모든 가능한 경우를 고려하여 원래의 정리를 증명하는 방법이다. 전수 증명은 경우에 의한 증명의 특수한 경우이다.

---

## 4-5.3 Lean4에서 전수 증명 구현

### Lean4의 결정 가능 명제

Lean4에서 유한한 범위의 명제는 `Decidable` 타입 클래스를 통해 자동으로 검사할 수 있다.

```lean
-- 전수 증명을 위한 기본 도구들
#check @decide      -- 결정 가능한 명제의 참/거짓 판별
#check Decidable    -- 결정 가능 타입 클래스
```

### 예제: 작은 범위의 전수 검사

```lean
-- 예제 1: n ≤ 4인 양의 정수에 대해 (n+1)³ ≥ 3n 증명
-- Lean4에서는 Fin 타입을 사용하여 유한 범위를 표현

-- 방법 1: 개별 검사
example : (1 + 1)^3 ≥ 3 * 1 := by native_decide
example : (2 + 1)^3 ≥ 3 * 2 := by native_decide
example : (3 + 1)^3 ≥ 3 * 3 := by native_decide
example : (4 + 1)^3 ≥ 3 * 4 := by native_decide

-- 방법 2: decide 전술 사용 (작은 유한 범위)
example : ∀ n : Fin 5, n.val ≠ 0 → (n.val + 1)^3 ≥ 3 * n.val := by
  decide
```

### `decide`와 `native_decide`의 차이

| 전술 | 설명 | 사용 시점 |
|-----|------|---------|
| `decide` | Lean 내부에서 계산하여 판정 | 작은 유한 범위의 명제 |
| `native_decide` | 네이티브 코드로 컴파일하여 판정 | 더 큰 범위, 더 빠른 계산 필요 시 |

### 연습문제 1: 전수 증명 기초

다음 명제들이 참임을 `native_decide`를 사용하여 증명하라.

```lean
-- 연습 1-1: 1부터 3까지의 자연수에 대해 n² ≥ n 성립
example : (1 : Nat)^2 ≥ 1 := by sorry
example : (2 : Nat)^2 ≥ 2 := by sorry
example : (3 : Nat)^2 ≥ 3 := by sorry
```

<details>
<summary>답 보기</summary>

```lean
example : (1 : Nat)^2 ≥ 1 := by native_decide
example : (2 : Nat)^2 ≥ 2 := by native_decide
example : (3 : Nat)^2 ≥ 3 := by native_decide
```

**설명**: `native_decide`는 수치 계산이 포함된 결정 가능한 명제를 자동으로 검증한다.

</details>

---

## 4-5.4 경우에 의한 증명의 원리

### 기본 형태

경우에 의한 증명은 다음 형태의 추론 규칙을 기반으로 한다:

$$\frac{(p_1 \vee p_2) \quad (p_1 \rightarrow q) \quad (p_2 \rightarrow q)}{q}$$

이것은 "두 경우 중 하나가 반드시 성립하고, 각 경우에서 $q$가 따라나온다면, $q$가 참이다"라는 의미이다.

### 예제 3 (Rosen 1.8절)

**문제**: $n$이 정수이면 $n^2 \geq n$임을 증명하라.

**풀이**: 세 가지 경우로 나눈다.

- **경우 (i)**: $n = 0$일 때, $0^2 = 0 \geq 0$. ✓
- **경우 (ii)**: $n \geq 1$일 때, $n^2 = n \cdot n \geq n \cdot 1 = n$. ✓
- **경우 (iii)**: $n \leq -1$일 때, $n^2 \geq 0 > n$이므로 $n^2 \geq n$. ✓

세 경우가 모든 정수를 망라하고, 각 경우에서 $n^2 \geq n$이 성립하므로 증명 완료.

---

## 4-5.5 Lean4에서 경우에 의한 증명

### `cases` 전술

`cases` 전술은 가설이나 데이터 타입을 경우별로 분해한다.

```lean
-- 기본 문법
-- cases h          -- 가설 h를 경우별로 분해
-- cases h with     -- 분해 후 이름 지정
--   | case1 => ...
--   | case2 => ...
```

### 논리합(Or)에 대한 경우 분해

```lean
-- P ∨ Q가 가설로 주어졌을 때 두 경우로 나누기
example (P Q R : Prop) (h : P ∨ Q) (hp : P → R) (hq : Q → R) : R := by
  cases h with
  | inl p => exact hp p    -- P인 경우: P → R 적용
  | inr q => exact hq q    -- Q인 경우: Q → R 적용
```

### `rcases`와 패턴 매칭

`rcases`는 더 유연한 패턴 매칭을 제공한다.

```lean
-- rcases 사용 예
example (P Q R : Prop) (h : P ∨ Q) (hp : P → R) (hq : Q → R) : R := by
  rcases h with p | q
  · exact hp p
  · exact hq q
```

### 예제: 정수의 부호에 따른 경우 분해

```lean
-- 정수가 양수, 0, 음수 중 하나임을 이용한 경우 분해
-- Int.lt_trichotomy: ∀ a b : Int, a < b ∨ a = b ∨ a > b

example (n : Int) : n * n ≥ 0 := by
  -- n ≥ 0 또는 n < 0으로 나눔
  rcases le_or_lt 0 n with h | h
  · -- n ≥ 0인 경우
    exact mul_nonneg h h
  · -- n < 0인 경우
    have hn : n ≤ 0 := le_of_lt h
    exact mul_nonneg_of_nonpos_nonpos hn hn
```

### 연습문제 2: 경우에 의한 증명

다음 명제들을 경우에 의한 증명으로 완성하라.

```lean
-- 연습 2-1: 논리합에서 경우 분해
example (P Q : Prop) (h : P ∨ Q) : Q ∨ P := by
  cases h with
  | inl hp => sorry  -- P인 경우
  | inr hq => sorry  -- Q인 경우
```

<details>
<summary>답 보기</summary>

```lean
example (P Q : Prop) (h : P ∨ Q) : Q ∨ P := by
  cases h with
  | inl hp => right; exact hp  -- P인 경우: Q ∨ P의 오른쪽(P)
  | inr hq => left; exact hq   -- Q인 경우: Q ∨ P의 왼쪽(Q)
```

**설명**:
- `inl hp`: `h : P ∨ Q`에서 왼쪽(P)인 경우, `hp : P`를 얻음
- `inr hq`: 오른쪽(Q)인 경우, `hq : Q`를 얻음
- `right`: `Q ∨ P`의 오른쪽을 선택 (P를 증명해야 함)
- `left`: `Q ∨ P`의 왼쪽을 선택 (Q를 증명해야 함)

</details>

```lean
-- 연습 2-2: 세 가지 경우로 분해
example (P Q R S : Prop) (h : P ∨ Q ∨ R) 
    (hp : P → S) (hq : Q → S) (hr : R → S) : S := by
  rcases h with p | q | r
  · sorry  -- P인 경우
  · sorry  -- Q인 경우
  · sorry  -- R인 경우
```

<details>
<summary>답 보기</summary>

```lean
example (P Q R S : Prop) (h : P ∨ Q ∨ R) 
    (hp : P → S) (hq : Q → S) (hr : R → S) : S := by
  rcases h with p | q | r
  · exact hp p  -- P인 경우
  · exact hq q  -- Q인 경우
  · exact hr r  -- R인 경우
```

**설명**: `rcases h with p | q | r`은 `P ∨ Q ∨ R`을 세 가지 경우로 분해한다. 각 경우에서 해당하는 함수를 적용하여 `S`를 도출한다.

</details>

---

## 4-5.6 일반성을 잃지 않고(WLOG)

### 개념 설명

**일반성을 잃지 않고**(Without Loss Of Generality, WLOG)는 증명에서 필요로 하는 경우의 수를 줄이기 위한 가정이다.

예를 들어, "실수 $x$와 $y$에 대해 어떤 성질 $P(x, y)$를 증명하라"는 문제에서, $P(x, y)$와 $P(y, x)$가 본질적으로 같다면, "일반성을 잃지 않고 $x \leq y$라고 가정"할 수 있다.

### 예제 4 (Rosen 1.8절)

**문제**: $|xy| = |x||y|$임을 경우에 의한 증명 방법으로 증명하라.

**분석**: $x$와 $y$의 부호에 따라 네 가지 경우가 있다:
- (i) $x \geq 0$, $y \geq 0$
- (ii) $x \geq 0$, $y < 0$
- (iii) $x < 0$, $y \geq 0$
- (iv) $x < 0$, $y < 0$

그러나 (ii)와 (iii)은 $x$와 $y$의 역할을 바꾸면 같으므로, **일반성을 잃지 않고** (iii)을 생략할 수 있다.

### Lean4에서 WLOG

Lean4의 Mathlib 라이브러리에는 `wlog` 전술이 있다:

```lean
-- wlog 전술 사용 예 (Mathlib 필요)
-- import Mathlib.Tactic.WLOG

-- wlog h : x ≤ y with H
-- · -- x ≤ y를 가정한 경우 증명
-- · -- H를 이용하여 y ≤ x인 경우로 귀결
```

### 연습문제 3: 대칭성 활용

```lean
-- 연습 3-1: P(a, b) ↔ P(b, a)일 때 대칭성 활용
-- 힌트: 조건을 잘 설정하면 경우의 수를 줄일 수 있다

example (a b : Nat) (h : a + b = 10) : b + a = 10 := by
  sorry
```

<details>
<summary>답 보기</summary>

```lean
example (a b : Nat) (h : a + b = 10) : b + a = 10 := by
  rw [Nat.add_comm]
  exact h
```

**설명**: `Nat.add_comm : ∀ a b, a + b = b + a`를 사용하여 `b + a`를 `a + b`로 재작성한다. 덧셈의 교환법칙이 대칭성의 예이다.

</details>

---

## 4-5.7 존재 증명: 생산적 증명과 비생산적 증명

### 존재 증명이란?

많은 정리가 "어떤 조건을 만족시키는 특수한 객체가 존재한다"는 것을 주장한다. 이런 형태의 정리를 **존재 증명**(existence proof)이라 한다.

형식적으로, $\exists x P(x)$의 존재 증명은 $P(a)$가 참인 어떤 원소 $a$를 구함으로써 완료할 수 있다. 이 원소 $a$를 **증인**(witness)이라 한다.

### 생산적 증명 vs 비생산적 증명

| 유형 | 설명 | 예시 |
|-----|------|-----|
| **생산적**(constructive) | 실제로 증인을 찾아냄 | "$x = 2$가 $x^2 = 4$를 만족" |
| **비생산적**(nonconstructive) | 존재는 보이지만 구체적 예시 없음 | 모순에 의한 존재 증명 |

### 예제 10 (Rosen 1.8절): 생산적 존재 증명

**문제**: 두 가지 다른 형태로 양의 정수 3제곱들의 합으로 나타낼 수 있는 양의 정수가 존재함을 증명하라.

**풀이**: 
$$1729 = 10^3 + 9^3 = 12^3 + 1^3$$

1729가 두 가지 방법으로 두 3제곱수의 합으로 표현될 수 있으므로 증명이 완료되었다. (이것은 **라마누잔 수**로 알려져 있다!)

### 예제 11 (Rosen 1.8절): 비생산적 존재 증명

**문제**: $x^y$가 유리수가 되는 무리수 $x$와 $y$가 존재함을 증명하라.

**풀이**: $\sqrt{2}^{\sqrt{2}}$를 생각해 보자. 두 가지 경우가 있다:

1. 만약 $\sqrt{2}^{\sqrt{2}}$가 유리수라면, $x = y = \sqrt{2}$가 원하는 예.
2. 만약 $\sqrt{2}^{\sqrt{2}}$가 무리수라면, $x = \sqrt{2}^{\sqrt{2}}$, $y = \sqrt{2}$로 놓으면:
   $$x^y = (\sqrt{2}^{\sqrt{2}})^{\sqrt{2}} = \sqrt{2}^{\sqrt{2} \cdot \sqrt{2}} = \sqrt{2}^2 = 2$$
   이므로 유리수이다.

두 경우 중 하나가 반드시 성립하므로 존재가 증명되었다. 그러나 **어느 경우인지는 모른다**!

---

## 4-5.8 Lean4에서 존재 증명

### `use` 전술: 증인 제공

`use` 전술은 존재 명제를 증명할 때 구체적인 증인을 제공한다.

```lean
-- ∃ x, P(x)를 증명하려면:
-- use a          -- a가 증인임을 선언
-- -- 이제 P(a)를 증명해야 함
```

### 기본 예제

```lean
-- 예제: x + 3 = 5를 만족하는 자연수 x가 존재한다
example : ∃ x : Nat, x + 3 = 5 := by
  use 2        -- 증인으로 2를 제시
  -- 이제 2 + 3 = 5를 증명
  native_decide

-- 예제: 짝수가 존재한다 (Even의 정의: ∃ k, n = 2 * k)
example : ∃ n : Nat, ∃ k : Nat, n = 2 * k := by
  use 4        -- n = 4
  use 2        -- k = 2
  rfl          -- 4 = 2 * 2
```

### 라마누잔 수 예제

```lean
-- 1729 = 10³ + 9³ = 12³ + 1³ 검증
example : 10^3 + 9^3 = 1729 := by native_decide
example : 12^3 + 1^3 = 1729 := by native_decide

-- 두 가지 다른 방법으로 두 3제곱의 합으로 나타낼 수 있는 수가 존재
example : ∃ n : Nat, ∃ a b c d : Nat, 
    a ≠ c ∧ n = a^3 + b^3 ∧ n = c^3 + d^3 := by
  use 1729, 10, 9, 12, 1
  native_decide
```

### `obtain`으로 존재 명제 분해

존재 명제가 가설로 주어졌을 때, `obtain`을 사용하여 증인과 성질을 추출한다.

```lean
-- h : ∃ x, P(x)가 주어졌을 때
-- obtain ⟨a, ha⟩ := h
-- 이제 a : 타입, ha : P(a)를 사용 가능
```

### 연습문제 4: 존재 증명

```lean
-- 연습 4-1: 3보다 큰 소수가 존재한다
-- 힌트: 5는 소수이다
example : ∃ p : Nat, p > 3 ∧ Nat.Prime p := by
  sorry
```

<details>
<summary>답 보기</summary>

```lean
example : ∃ p : Nat, p > 3 ∧ Nat.Prime p := by
  use 5
  constructor
  · native_decide          -- 5 > 3
  · native_decide          -- 5는 소수
```

**설명**:
- `use 5`: 증인으로 5를 제시
- `constructor`: 논리곱 `∧`을 두 부분으로 분리
- 각 부분을 `native_decide`로 자동 검증

</details>

```lean
-- 연습 4-2: 존재 명제 분해
example (h : ∃ x : Nat, x * x = 16) : ∃ y : Nat, y = 4 := by
  obtain ⟨x, hx⟩ := h
  sorry
```

<details>
<summary>답 보기</summary>

```lean
example (h : ∃ x : Nat, x * x = 16) : ∃ y : Nat, y = 4 := by
  obtain ⟨x, hx⟩ := h
  use 4
  rfl
```

**설명**: 이 예제에서 `h`에서 추출한 `x`를 직접 사용하지는 않지만, 존재 명제를 분해하는 패턴을 보여준다. 증인 `4`를 직접 제시하여 `y = 4`를 증명한다.

</details>

```lean
-- 연습 4-3: 존재의 전이
-- 만약 모든 x에 대해 P(x) → Q(x)이고, P(a)를 만족하는 a가 존재하면,
-- Q(b)를 만족하는 b가 존재한다
example (P Q : Nat → Prop) 
    (h1 : ∀ x, P x → Q x) 
    (h2 : ∃ a, P a) : ∃ b, Q b := by
  obtain ⟨a, ha⟩ := h2
  sorry
```

<details>
<summary>답 보기</summary>

```lean
example (P Q : Nat → Prop) 
    (h1 : ∀ x, P x → Q x) 
    (h2 : ∃ a, P a) : ∃ b, Q b := by
  obtain ⟨a, ha⟩ := h2
  use a                    -- a를 증인으로 사용
  exact h1 a ha            -- h1 a : P a → Q a에 ha : P a 적용
```

**설명**:
- `obtain ⟨a, ha⟩ := h2`: `∃ a, P a`에서 증인 `a`와 `ha : P a` 추출
- `use a`: `∃ b, Q b`의 증인으로 `a` 제시
- `h1 a ha`: `P a → Q a`에 `P a`를 적용하여 `Q a` 도출

</details>

---

## 4-5.9 유일성 증명

### 유일성 증명이란?

정리 중에는 "유일하게 하나의 요소만이 주어진 특성을 갖고 있다"고 주장하는 것들이 있다. 이런 형태의 정리를 증명하기 위해서는 **하나의 요소만이** 주어진 특성을 갖고 있음을 보여야 한다.

**유일성 증명**(uniqueness proof)은 두 부분으로 나누어진다:

1. **존재성**: $x$가 주어진 특성을 갖고 있음을 보인다.
2. **유일성**: 만약 $x$와 $y$가 둘 다 주어진 특성을 갖는다면 $x = y$임을 보인다.

### 유일 존재 한정기호: ∃!

수학에서 "유일하게 존재한다"를 나타내는 기호는 $\exists!$ 이다.

$$\exists! x \, P(x) \iff \exists x (P(x) \wedge \forall y (P(y) \rightarrow y = x))$$

이것은 "정확히 하나의 $x$가 $P(x)$를 만족한다"를 의미한다.

### 예제 13 (Rosen 1.8절)

**문제**: $a$와 $b$가 실수이고 $a \neq 0$이면 $ar + b = 0$을 만족하는 유일한 실수 $r$이 존재함을 증명하라.

**풀이**:

1. **존재성**: $r = -b/a$가 $ar + b = 0$의 해임을 알 수 있다.
   $$a(-b/a) + b = -b + b = 0$$

2. **유일성**: $as + b = 0$을 만족하는 실수 $s$가 존재한다고 가정하자.
   그러면 $ar + b = as + b$이고, 양변에서 $b$를 빼면 $ar = as$.
   $a \neq 0$이므로 양변을 $a$로 나누면 $r = s$.

따라서 유일성이 증명되었다.

---

## 4-5.10 Lean4에서 유일성 증명

### `∃!` 기호와 `ExistsUnique`

Lean4에서 유일 존재는 `∃!` 또는 `ExistsUnique`로 표현한다.

```lean
-- ∃! x, P x 의 정의
-- ExistsUnique (fun x => P x)
-- 이것은 다음과 동치: ∃ x, P x ∧ ∀ y, P y → y = x

#check ExistsUnique  -- (α → Prop) → Prop
```

### 유일성 증명 구조

```lean
-- ∃! x, P x를 증명하려면:
example (P : Nat → Prop) : ∃! x, P x := by
  use 42                           -- 1. 증인 제시
  constructor
  · -- P 42 증명 (존재성)
    sorry
  · -- ∀ y, P y → y = 42 증명 (유일성)
    intro y hy
    sorry
```

### 예제: 간단한 유일성 증명

```lean
-- x + 3 = 5를 만족하는 유일한 자연수 x가 존재
example : ∃! x : Nat, x + 3 = 5 := by
  use 2
  constructor
  · -- 2 + 3 = 5
    rfl
  · -- ∀ y, y + 3 = 5 → y = 2
    intro y hy
    -- y + 3 = 5에서 y = 2 유도
    omega  -- 선형 산술 해결

-- 더 명시적인 방법
example : ∃! x : Nat, x + 3 = 5 := by
  use 2
  constructor
  · rfl
  · intro y hy
    -- hy : y + 3 = 5
    -- 양변에서 3을 빼면 y = 2
    have : y = 5 - 3 := by omega
    simp at this
    exact this
```

### `∃!` 분해하기

유일 존재 명제가 가설로 주어졌을 때:

```lean
-- h : ∃! x, P x가 주어졌을 때 분해
example (P : Nat → Prop) (h : ∃! x, P x) : ∃ x, P x := by
  -- 존재성만 추출
  exact h.exists

example (P : Nat → Prop) (h : ∃! x, P x) (a b : Nat) 
    (ha : P a) (hb : P b) : a = b := by
  -- 유일성 사용
  exact h.unique ha hb
```

### 연습문제 5: 유일성 증명

```lean
-- 연습 5-1: x * 1 = 5를 만족하는 유일한 자연수
example : ∃! x : Nat, x * 1 = 5 := by
  use 5
  constructor
  · sorry  -- 5 * 1 = 5
  · intro y hy
    sorry  -- y * 1 = 5 → y = 5
```

<details>
<summary>답 보기</summary>

```lean
example : ∃! x : Nat, x * 1 = 5 := by
  use 5
  constructor
  · rfl                    -- 5 * 1 = 5
  · intro y hy
    simp at hy             -- y * 1 = y이므로 hy : y = 5
    exact hy
```

**설명**:
- `rfl`: `5 * 1 = 5`는 정의상 참
- `simp at hy`: `y * 1 = 5`를 단순화하면 `y = 5`
- `exact hy`: 목표와 일치

</details>

```lean
-- 연습 5-2: 유일 존재에서 존재성 추출
example (P : Nat → Prop) (h : ∃! x, P x) : ∃ x, P x := by
  sorry
```

<details>
<summary>답 보기</summary>

```lean
example (P : Nat → Prop) (h : ∃! x, P x) : ∃ x, P x := by
  exact h.exists
  -- 또는
  -- obtain ⟨x, hx, _⟩ := h
  -- use x
  -- exact hx
```

**설명**: `h.exists`는 `∃! x, P x`에서 존재성 부분 `∃ x, P x`를 추출한다.

</details>

---

## 4-5.11 증명 전략: 전향 추론과 후향 추론

### 전향 추론(Forward Reasoning)

**전향 추론**은 전제로부터 시작하여 공리들과 알려진 정리들을 이용하여 결론에 도달하는 방법이다.

```
전제 → 중간 단계들 → 결론
```

Lean4에서 전향 추론:
```lean
example (P Q R : Prop) (hp : P) (hpq : P → Q) (hqr : Q → R) : R := by
  -- 전향 추론: P에서 시작하여 R에 도달
  have hq : Q := hpq hp     -- P → Q에 P 적용하여 Q 얻음
  have hr : R := hqr hq     -- Q → R에 Q 적용하여 R 얻음
  exact hr
```

### 후향 추론(Backward Reasoning)

**후향 추론**은 결론에서 시작하여 결론을 참으로 만들 수 있는 전제를 찾아가는 방법이다.

```
결론 ← 이것을 증명하려면? ← 전제
```

Lean4에서 후향 추론:
```lean
example (P Q R : Prop) (hp : P) (hpq : P → Q) (hqr : Q → R) : R := by
  -- 후향 추론: R을 증명하려면 Q가 필요
  apply hqr        -- R을 증명하려면 Q를 증명해야 함
  apply hpq        -- Q를 증명하려면 P를 증명해야 함
  exact hp         -- P는 가설로 주어짐
```

### 예제 14 (Rosen 1.8절): 산술평균-기하평균 부등식

**문제**: 서로 다른 양의 실수 $x$와 $y$에 대해 산술평균 $(x+y)/2$가 기하평균 $\sqrt{xy}$보다 항상 크다는 것을 증명하라.

**후향 추론 적용**:

$$\frac{x+y}{2} > \sqrt{xy}$$

를 증명하려면, 다음과 같이 **동치인 부등식들**을 거꾸로 추적한다:

1. $(x+y)/2 > \sqrt{xy}$
2. $(x+y)^2/4 > xy$ (양변 제곱)
3. $(x+y)^2 > 4xy$
4. $x^2 + 2xy + y^2 > 4xy$
5. $x^2 - 2xy + y^2 > 0$
6. $(x-y)^2 > 0$ ← $x \neq y$이면 항상 참!

이제 **전향 추론**으로 증명을 완성한다 (역순으로).

### 연습문제 6: 추론 방향

```lean
-- 연습 6-1: 전향 추론으로 증명
example (P Q R S : Prop) (hp : P) (hpq : P → Q) (hqr : Q → R) (hrs : R → S) : S := by
  -- 전향 추론 사용
  have hq : Q := sorry
  have hr : R := sorry
  have hs : S := sorry
  exact hs
```

<details>
<summary>답 보기</summary>

```lean
example (P Q R S : Prop) (hp : P) (hpq : P → Q) (hqr : Q → R) (hrs : R → S) : S := by
  have hq : Q := hpq hp
  have hr : R := hqr hq
  have hs : S := hrs hr
  exact hs
```

**설명**: 각 `have` 문은 전향 추론의 단계이다. `P`에서 시작하여 `Q`, `R`, `S`로 진행한다.

</details>

```lean
-- 연습 6-2: 후향 추론으로 같은 명제 증명
example (P Q R S : Prop) (hp : P) (hpq : P → Q) (hqr : Q → R) (hrs : R → S) : S := by
  -- 후향 추론 사용 (apply 연쇄)
  sorry
```

<details>
<summary>답 보기</summary>

```lean
example (P Q R S : Prop) (hp : P) (hpq : P → Q) (hqr : Q → R) (hrs : R → S) : S := by
  apply hrs          -- S를 증명하려면 R 필요
  apply hqr          -- R을 증명하려면 Q 필요
  apply hpq          -- Q를 증명하려면 P 필요
  exact hp           -- P는 가설
```

**설명**: `apply`는 목표를 변환한다. `S`에서 시작하여 점점 단순한 목표로 변환한다.

</details>

---

## 4-5.12 반례 찾기

### 반례란?

**반례**(counterexample)는 전칭 명제 $\forall x \, P(x)$가 거짓임을 보이기 위해 사용된다. $P(a)$가 거짓인 특정 값 $a$를 찾으면 된다.

$$\neg(\forall x \, P(x)) \iff \exists x \, \neg P(x)$$

### 예제 17 (Rosen 1.8절)

**문제**: "모든 양의 정수는 두 정수의 제곱의 합으로 나타낼 수 있다"가 거짓임을 보여라.

**반례**: $7 = 0^2 + ?$를 검토하면:
- $0^2 = 0$, $1^2 = 1$, $2^2 = 4$ 뿐이고
- $7 - 0 = 7$ (제곱수 아님), $7 - 1 = 6$ (제곱수 아님), $7 - 4 = 3$ (제곱수 아님)

따라서 $7$은 두 제곱수의 합으로 나타낼 수 없다. 반례가 존재하므로 원래 명제는 **거짓**이다.

### 가설을 세우고 반례 찾기

가설이 참인지 확인하려면:
1. 먼저 가설을 **증명하려고** 시도한다.
2. 실패하면 **반례를 찾아** 가설이 거짓임을 보인다.
3. 반례를 찾을 수 없으면 다시 증명을 시도한다.

---

## 4-5.13 Lean4에서 반례 표현

### 명제의 부정 증명

반례를 찾는 것은 $\exists x \, \neg P(x)$를 증명하는 것과 같다.

```lean
-- "모든 자연수 n에 대해 n < 5"가 거짓임을 증명
-- 반례: n = 5
example : ¬(∀ n : Nat, n < 5) := by
  intro h              -- 가정: ∀ n, n < 5
  have : 5 < 5 := h 5  -- n = 5 대입
  omega                -- 5 < 5는 모순

-- 존재 형식으로 반례 표현
example : ∃ n : Nat, ¬(n < 5) := by
  use 5
  omega  -- ¬(5 < 5)는 참
```

### 전수 검사로 반례 없음 확인

```lean
-- 1 ≤ n ≤ 4인 모든 n에 대해 n² < 20임을 검증
example : ∀ n : Fin 5, n.val ≠ 0 → n.val^2 < 20 := by
  decide  -- 모든 경우 검사
```

### 연습문제 7: 반례 찾기

```lean
-- 연습 7-1: "모든 자연수는 10보다 작다"의 반례
example : ∃ n : Nat, ¬(n < 10) := by
  sorry
```

<details>
<summary>답 보기</summary>

```lean
example : ∃ n : Nat, ¬(n < 10) := by
  use 10
  omega
```

**설명**: $n = 10$은 $10 < 10$이 아니므로 반례이다.

</details>

```lean
-- 연습 7-2: "모든 자연수 n에 대해 n² = n"의 반례
example : ∃ n : Nat, n^2 ≠ n := by
  sorry
```

<details>
<summary>답 보기</summary>

```lean
example : ∃ n : Nat, n^2 ≠ n := by
  use 2
  native_decide  -- 2² = 4 ≠ 2
```

**설명**: $2^2 = 4 \neq 2$이므로 $n = 2$가 반례이다.

</details>

---

## 4-5.14 종합 연습문제

이제 배운 모든 증명 방법을 종합적으로 연습해 보자.

### 연습문제 8: 경우에 의한 증명 종합

```lean
-- 연습 8-1: n이 정수이면 n(n+1)은 짝수이다
-- 힌트: n이 짝수이거나 홀수임을 이용
-- Even n ↔ ∃ k, n = 2 * k
-- Odd n ↔ ∃ k, n = 2 * k + 1

example (n : Int) : Even (n * (n + 1)) := by
  -- n이 짝수이거나 홀수
  rcases Int.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · -- n이 짝수인 경우: n = 2k
    sorry
  · -- n이 홀수인 경우: n = 2k + 1
    sorry
```

<details>
<summary>답 보기</summary>

```lean
example (n : Int) : Even (n * (n + 1)) := by
  rcases Int.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · -- n이 짝수인 경우: n = 2k
    use k * (n + 1)
    rw [hk]
    ring
  · -- n이 홀수인 경우: n = 2k + 1
    -- 그러면 n + 1 = 2k + 2 = 2(k + 1)은 짝수
    use n * (k + 1)
    rw [hk]
    ring
```

**설명**:
- 짝수인 경우: $n(n+1) = 2k(n+1) = 2 \cdot k(n+1)$
- 홀수인 경우: $n(n+1) = (2k+1)(2k+2) = 2(2k+1)(k+1)$

</details>

### 연습문제 9: 존재 증명 종합

```lean
-- 연습 9-1: 어떤 자연수의 제곱은 그 자연수 자신과 같다
-- (0² = 0, 1² = 1)
example : ∃ n : Nat, n^2 = n := by
  sorry
```

<details>
<summary>답 보기</summary>

```lean
example : ∃ n : Nat, n^2 = n := by
  use 1
  native_decide  -- 1² = 1
  -- 또는 use 0; native_decide
```

</details>

```lean
-- 연습 9-2: 연속하는 두 자연수의 합이 홀수인 경우가 존재
example : ∃ n : Nat, Odd (n + (n + 1)) := by
  sorry
```

<details>
<summary>답 보기</summary>

```lean
example : ∃ n : Nat, Odd (n + (n + 1)) := by
  use 0
  -- 0 + 1 = 1은 홀수
  use 0
  ring
```

**설명**: $n + (n+1) = 2n + 1$은 항상 홀수이다. $n = 0$일 때 $1 = 2 \cdot 0 + 1$.

</details>

### 연습문제 10: 유일성 증명 종합

```lean
-- 연습 10-1: 방정식 2x + 4 = 10의 유일한 자연수 해
example : ∃! x : Nat, 2 * x + 4 = 10 := by
  use 3
  constructor
  · sorry  -- 2 * 3 + 4 = 10
  · intro y hy
    sorry  -- 2 * y + 4 = 10 → y = 3
```

<details>
<summary>답 보기</summary>

```lean
example : ∃! x : Nat, 2 * x + 4 = 10 := by
  use 3
  constructor
  · native_decide  -- 2 * 3 + 4 = 10
  · intro y hy
    omega          -- 선형 방정식 풀이
```

</details>

---

## 4-5.15 도전 문제

### 도전 1: 완전 제곱수 존재 증명 (Rosen 예제 2 변형)

100을 넘지 않는 연속적인 양의 정수 중 완전 제곱수가 되는 쌍이 존재함을 증명하라.

```lean
-- 완전 제곱수 정의: ∃ m, n = m^2
def IsPerfectSquare (n : Nat) : Prop := ∃ m : Nat, n = m^2

-- 8과 9가 연속하고 9가 완전 제곱수임을 보이기
example : ∃ n : Nat, n < 100 ∧ IsPerfectSquare (n + 1) := by
  sorry
```

<details>
<summary>답 보기</summary>

```lean
example : ∃ n : Nat, n < 100 ∧ IsPerfectSquare (n + 1) := by
  use 8
  constructor
  · native_decide  -- 8 < 100
  · use 3          -- 9 = 3²
    native_decide
```

**설명**: $n = 8$일 때 $n + 1 = 9 = 3^2$는 완전 제곱수이다.

</details>

### 도전 2: 절댓값 성질 (Rosen 예제 4 변형)

```lean
-- |x * y| = |x| * |y| 증명 (정수에서)
-- Int.natAbs : Int → Nat

example (x y : Int) : Int.natAbs (x * y) = Int.natAbs x * Int.natAbs y := by
  sorry
```

<details>
<summary>답 보기</summary>

```lean
example (x y : Int) : Int.natAbs (x * y) = Int.natAbs x * Int.natAbs y := by
  exact Int.natAbs_mul x y
```

**설명**: Mathlib에는 이 정리가 `Int.natAbs_mul`로 이미 증명되어 있다. 직접 증명하려면 경우에 의한 증명으로 $x, y$의 부호를 나누어야 한다.

</details>

### 도전 3: 비둘기집 원리 응용

```lean
-- 22일 중 같은 요일인 날이 적어도 4일 존재
-- (일주일은 7일이므로, 22 = 7 × 3 + 1)

-- 비둘기집 원리: n + 1개의 물건을 n개의 상자에 넣으면
-- 적어도 하나의 상자에 2개 이상의 물건이 있다

-- 간단한 형태로 표현
example : ∀ f : Fin 22 → Fin 7, ∃ d : Fin 7, ∃ i j : Fin 22, i ≠ j ∧ f i = d ∧ f j = d := by
  sorry  -- 이 증명은 고급 수준
```

<details>
<summary>힌트</summary>

비둘기집 원리의 완전한 Lean4 증명은 Mathlib의 `Finset.exists_ne_map_eq_of_card_lt_of_maps_to`를 사용한다. 기본적인 아이디어는 22개의 날을 7개의 요일에 배정하면, 평균적으로 각 요일에 $22/7 \approx 3.14$일이 배정되므로 적어도 하나의 요일에 4일 이상이 배정된다는 것이다.

</details>

---

## 4-5.16 요약

### 증명 방법 비교표

| 증명 방법 | 언제 사용? | Lean4 핵심 전술 |
|--------|---------|-------------|
| **전수 증명** | 유한하고 적은 경우의 수 | `decide`, `native_decide` |
| **경우에 의한 증명** | 여러 경우로 분리 가능할 때 | `cases`, `rcases` |
| **존재 증명 (생산적)** | 증인을 직접 찾을 수 있을 때 | `use` |
| **존재 증명 (비생산적)** | 존재는 알지만 구체적 예 없을 때 | 간접 논증 |
| **유일성 증명** | 정확히 하나임을 보일 때 | `use`, `h.unique` |
| **반례** | 전칭 명제의 거짓 증명 | `use` (부정의 증인) |

### 주요 Lean4 전술 정리

| 전술 | 용도 | 예시 |
|-----|------|-----|
| `decide` | 결정 가능한 명제 자동 판정 | `example : 2 + 2 = 4 := by decide` |
| `native_decide` | 더 빠른 결정 판정 | `example : 100! > 0 := by native_decide` |
| `cases h` | 가설 h를 경우별로 분해 | `cases h with \| inl a => ... \| inr b => ...` |
| `rcases h with p \| q` | 패턴 매칭으로 분해 | `rcases h with ⟨a, ha⟩` |
| `use a` | 존재 명제의 증인 제시 | `use 42` |
| `obtain ⟨x, hx⟩ := h` | 존재 명제에서 증인 추출 | 가설 분해 |
| `h.exists` | `∃!`에서 존재성 추출 | 유일 존재 → 존재 |
| `h.unique` | `∃!`에서 유일성 추출 | 두 증인의 동치성 |

### → vs ↔ 복습 (Part 4-4)

| 기호 | 의미 | Lean4 분해 |
|-----|------|----------|
| `→` | "이면" (조건문) | `intro`, `apply`, 함수 적용 |
| `↔` | "동치" (쌍조건문) | `.mp`, `.mpr`, `constructor` |

### 다음 장 예고

**Part 4-6**에서는 **수학적 귀납법**(Mathematical Induction)을 다룬다:
- 기본 귀납법의 원리
- Lean4의 `induction` 전술
- 강한 귀납법
- 구조적 귀납법

---

## 부록: 증명 방법 Lean4 전술 총정리

### A. 경우 분해 전술

```lean
-- 1. cases: 기본 경우 분해
example (P Q R : Prop) (h : P ∨ Q) (hp : P → R) (hq : Q → R) : R := by
  cases h with
  | inl p => exact hp p
  | inr q => exact hq q

-- 2. rcases: 재귀적 패턴 매칭
example (P Q R : Prop) (h : (P ∧ Q) ∨ R) : P ∨ R := by
  rcases h with ⟨p, q⟩ | r
  · left; exact p
  · right; exact r

-- 3. match: 함수형 패턴 매칭
example (P Q R : Prop) (h : P ∨ Q) (hp : P → R) (hq : Q → R) : R :=
  match h with
  | Or.inl p => hp p
  | Or.inr q => hq q
```

### B. 존재 관련 전술

```lean
-- 1. use: 증인 제공
example : ∃ x : Nat, x > 5 := by
  use 10
  native_decide

-- 2. obtain: 존재 분해
example (h : ∃ x : Nat, x > 5) : ∃ y : Nat, y > 4 := by
  obtain ⟨x, hx⟩ := h
  use x
  omega

-- 3. 유일 존재
example : ∃! x : Nat, x + 1 = 2 := by
  use 1
  simp
```

### C. 결정 가능성 전술

```lean
-- 1. decide: Lean 내부 계산
example : (3 : Nat) < 5 := by decide

-- 2. native_decide: 네이티브 코드 사용
example : (100 : Nat) * 100 = 10000 := by native_decide

-- 3. omega: 선형 산술 해결
example (n : Nat) (h : n > 5) : n ≥ 6 := by omega
```

### D. 종합 예제

```lean
-- 종합: 1 ≤ n ≤ 3인 모든 n에 대해 n² < 10이고,
--       n² < 10을 만족하는 n > 0이 유일하게 존재하지 않음을 보이기

-- 부분 1: 전수 증명
example : ∀ n : Fin 4, n.val ≠ 0 → n.val^2 < 10 := by decide

-- 부분 2: 유일하지 않음 (반례)
example : ¬(∃! n : Nat, n > 0 ∧ n^2 < 10) := by
  intro h
  have h1 : 1 > 0 ∧ 1^2 < 10 := by native_decide
  have h2 : 2 > 0 ∧ 2^2 < 10 := by native_decide
  have : 1 = 2 := h.unique h1 h2
  native_decide  -- 1 = 2는 거짓
```

---


