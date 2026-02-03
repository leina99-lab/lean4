# Lean4 완전 정복 가이드 — 제4-5편 (Part B)

## 증명 방법과 전략 완전 정복 (계속)

> **교재**: Kenneth H. Rosen, "Discrete Mathematics and Its Applications" 8판  
> **범위**: 1.8절 증명 방법과 전략  
> **선수 학습**: Part A (전수 증명, 경우에 의한 증명, 존재 증명)

---

## 4-5.12 유일성 증명

### 4-5.12.1 유일성이란?

**유일성**(uniqueness)은 "**정확히 하나만** 존재한다"는 주장이다.

$$\exists! x \, P(x) \iff \exists x (P(x) \wedge \forall y (P(y) \rightarrow y = x))$$

**기호 ∃!** 는 "유일하게 존재한다"(there exists a unique)를 의미한다.

### 4-5.12.2 유일성 증명의 구조

유일성 증명은 **두 부분**으로 구성된다:

| 단계 | 이름 | 내용 |
|------|------|------|
| 1 | **존재성**(Existence) | P(a)를 만족하는 원소 a가 **존재함**을 보인다 |
| 2 | **유일성**(Uniqueness) | P(a)와 P(b)가 **모두 참이면** a = b임을 보인다 |

### 4-5.12.3 교재 예제 13

> **예제 13** (Rosen 1.8절):  
> a와 b가 실수이고 a ≠ 0이면 ar + b = 0을 만족하는 **유일한** 실수 r이 존재함을 증명하라.

**1단계 (존재성)**: r = -b/a가 해이다.
$$a \cdot (-b/a) + b = -b + b = 0 \checkmark$$

**2단계 (유일성)**: as + b = 0도 만족한다고 가정하면:
- ar + b = 0, as + b = 0에서
- ar = as → r = s (a ≠ 0이므로)

---

## 4-5.13 Lean4에서 유일성 증명

### 4-5.13.1 기본 구조

```lean
-- ∃! x, P x를 증명하는 기본 구조
example : ∃! x : Nat, x + 3 = 5 := by
  use 2                       -- 1단계: 증인 제시
  constructor
  · native_decide             -- 2 + 3 = 5
  · intro y hy               -- 2단계: 유일성
    omega                     -- y + 3 = 5이면 y = 2
```

### 4-5.13.2 유일성에서 정보 추출

```lean
-- h.exists : ∃! → ∃ (존재 추출)
example (P : Nat → Prop) (h : ∃! x, P x) : ∃ x, P x := h.exists

-- h.unique : 두 증인이 같음
example (P : Nat → Prop) (h : ∃! x, P x) (a b : Nat) 
    (ha : P a) (hb : P b) : a = b := h.unique ha hb
```

---

### 4-5.13.3 연습문제 6: 유일성 증명

#### 연습 6-1: 기본 유일성
```lean
example : ∃! x : Nat, 2 * x = 6 := by
  use 3
  constructor
  · sorry   -- 2 * 3 = 6
  · intro y hy; sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
example : ∃! x : Nat, 2 * x = 6 := by
  use 3
  constructor
  · native_decide
  · intro y hy; omega
```
</details>

#### 연습 6-2: 유일 존재에서 존재 추출
```lean
example (P : Nat → Prop) (h : ∃! x, P x) : ∃ x, P x := by
  sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
example (P : Nat → Prop) (h : ∃! x, P x) : ∃ x, P x := 
  h.exists
```
</details>

#### 연습 6-3: 유일성 활용
```lean
example (P : Nat → Prop) (h : ∃! x, P x) (a b : Nat) 
    (ha : P a) (hb : P b) : a = b := by
  sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
example (P : Nat → Prop) (h : ∃! x, P x) (a b : Nat) 
    (ha : P a) (hb : P b) : a = b := 
  h.unique ha hb
```
</details>

---

## 4-5.14 전향 추론과 후향 추론

### 4-5.14.1 전향 추론(Forward Reasoning)

**전향 추론**은 **전제에서 시작**하여 **결론 방향으로** 추론한다.

```
전제 → 중간 결과 → 중간 결과 → ... → 결론
```

### 4-5.14.2 후향 추론(Backward Reasoning)

**후향 추론**은 **결론에서 시작**하여 **전제 방향으로** 추론한다.

```
결론 ← 이것이 필요 ← 이것이 필요 ← ... ← 전제
```

### 4-5.14.3 비교

| 구분 | 전향 추론 | 후향 추론 |
|------|---------|---------|
| **방향** | 전제 → 결론 | 결론 → 전제 |
| **Lean4 전술** | `have`, `let` | `apply`, `refine` |
| **장점** | 직관적 | 목표 지향적 |

### 4-5.14.4 Lean4에서 전향 추론

`have` 전술을 사용하여 **중간 결과를 쌓아간다**.

```lean
example (P Q R : Prop) (hp : P) (hpq : P → Q) (hqr : Q → R) : R := by
  have hq : Q := hpq hp      -- 1단계: P → Q에 P 적용 → Q
  have hr : R := hqr hq      -- 2단계: Q → R에 Q 적용 → R
  exact hr                    -- 결론: R
```

### 4-5.14.5 Lean4에서 후향 추론

`apply` 전술을 사용하여 **목표를 단순화**해 나간다.

```lean
example (P Q R : Prop) (hp : P) (hpq : P → Q) (hqr : Q → R) : R := by
  apply hqr      -- R을 증명하려면 Q가 필요
  apply hpq      -- Q를 증명하려면 P가 필요
  exact hp       -- P는 가설로 주어짐
```

---

### 4-5.14.6 연습문제 7: 추론 방향

#### 연습 7-1: 전향 추론
```lean
example (P Q R S : Prop) (hp : P) (hpq : P → Q) (hqr : Q → R) (hrs : R → S) : S := by
  have hq : Q := sorry
  have hr : R := sorry
  have hs : S := sorry
  exact hs
```

<details>
<summary>💡 답 보기</summary>

```lean
example (P Q R S : Prop) (hp : P) (hpq : P → Q) (hqr : Q → R) (hrs : R → S) : S := by
  have hq : Q := hpq hp
  have hr : R := hqr hq
  have hs : S := hrs hr
  exact hs
```
</details>

#### 연습 7-2: 후향 추론
```lean
example (P Q R S : Prop) (hp : P) (hpq : P → Q) (hqr : Q → R) (hrs : R → S) : S := by
  sorry  -- apply만 사용
```

<details>
<summary>💡 답 보기</summary>

```lean
example (P Q R S : Prop) (hp : P) (hpq : P → Q) (hqr : Q → R) (hrs : R → S) : S := by
  apply hrs
  apply hqr
  apply hpq
  exact hp
```
</details>

---

## 4-5.15 반례 찾기

### 4-5.15.1 반례란?

**반례**(counterexample)는 **전칭 명제가 거짓**임을 보이기 위해 사용한다.

$$\neg(\forall x \, P(x)) \iff \exists x \, \neg P(x)$$

"모든 x에 대해 P(x)"가 거짓임을 보이려면, P(a)가 **거짓인** 특정 a를 찾으면 된다!

### 4-5.15.2 교재 예제 17

**문제**: "모든 양의 정수는 두 정수의 제곱의 합으로 나타낼 수 있다"가 거짓임을 보여라.

**반례**: n = 7

7 = a² + b²를 만족하는 음이 아닌 정수 a, b가 있는가?

| a | a² | 7 - a² | 제곱수? |
|---|-----|--------|--------|
| 0 | 0 | 7 | ✗ |
| 1 | 1 | 6 | ✗ |
| 2 | 4 | 3 | ✗ |

**결론**: 7은 두 제곱수의 합으로 나타낼 수 없다!

### 4-5.15.3 Lean4에서 반례 표현

```lean
-- "모든 자연수 n에 대해 n < 5"가 거짓임을 증명
example : ¬(∀ n : Nat, n < 5) := by
  intro h              -- 가정: ∀ n, n < 5
  have : 5 < 5 := h 5  -- n = 5 대입
  omega                -- 5 < 5는 모순

-- 존재 형식으로 반례 표현
example : ∃ n : Nat, ¬(n < 5) := by
  use 5
  omega                -- ¬(5 < 5)
```

---

### 4-5.15.4 연습문제 8: 반례 찾기

#### 연습 8-1: 간단한 반례
```lean
example : ∃ n : Nat, ¬(n < 10) := by
  sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
example : ∃ n : Nat, ¬(n < 10) := by
  use 10
  omega
```
</details>

#### 연습 8-2: 제곱 관련 반례
```lean
example : ∃ n : Nat, n^2 ≠ n := by
  sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
example : ∃ n : Nat, n^2 ≠ n := by
  use 2
  native_decide   -- 4 ≠ 2
```
</details>

#### 연습 8-3: 전칭 부정
```lean
example : ¬(∀ n : Nat, n < 100) := by
  intro h
  sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
example : ¬(∀ n : Nat, n < 100) := by
  intro h
  have : 100 < 100 := h 100
  omega
```
</details>

---

## 4-5.16 종합 연습문제

### 연습 9-1: 전수 증명 종합
```lean
-- 1 ≤ n ≤ 5인 모든 n에 대해 n! ≤ n^n
-- 힌트: n!은 factorial
example : ∀ n : Fin 6, n.val ≠ 0 → Nat.factorial n.val ≤ n.val ^ n.val := by
  sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
example : ∀ n : Fin 6, n.val ≠ 0 → Nat.factorial n.val ≤ n.val ^ n.val := by
  decide
```
</details>

### 연습 9-2: 경우에 의한 증명 종합
```lean
-- (P → R) ∧ (Q → R) ∧ (P ∨ Q)이면 R
example (P Q R : Prop) (h : (P → R) ∧ (Q → R) ∧ (P ∨ Q)) : R := by
  rcases h with ⟨hpr, hqr, hpq⟩
  rcases hpq with hp | hq
  · sorry
  · sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
example (P Q R : Prop) (h : (P → R) ∧ (Q → R) ∧ (P ∨ Q)) : R := by
  rcases h with ⟨hpr, hqr, hpq⟩
  rcases hpq with hp | hq
  · exact hpr hp
  · exact hqr hq
```
</details>

### 연습 9-3: 존재와 유일성 종합
```lean
-- ∃! x, x * 1 = 3을 만족하는 자연수
example : ∃! x : Nat, x * 1 = 3 := by
  sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
example : ∃! x : Nat, x * 1 = 3 := by
  use 3
  constructor
  · native_decide
  · intro y hy
    simp at hy
    exact hy
```
</details>

### 연습 9-4: 반례와 부정 종합
```lean
-- "모든 자연수 n에 대해 n² < 2n + 1"이 거짓
example : ¬(∀ n : Nat, n^2 < 2 * n + 1) := by
  sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
example : ¬(∀ n : Nat, n^2 < 2 * n + 1) := by
  intro h
  have h3 : 3^2 < 2 * 3 + 1 := h 3
  -- 9 < 7은 거짓
  omega
```
</details>

---

## 4-5.17 전술 요약표

### 경우에 의한 증명 전술

| 전술 | 용도 | 예시 |
|-----|------|------|
| `cases h with` | 논리합/귀납타입 분해 | `cases h with \| inl p => ... \| inr q => ...` |
| `rcases h with p \| q` | 패턴 매칭 분해 | `rcases h with ⟨a, ha⟩ \| hb` |
| `left` | 논리합 왼쪽 선택 | `left; exact hp` |
| `right` | 논리합 오른쪽 선택 | `right; exact hq` |

### 존재 증명 전술

| 전술 | 용도 | 예시 |
|-----|------|------|
| `use a` | 존재 증인 제시 | `use 42` |
| `obtain ⟨x, hx⟩ := h` | 존재에서 추출 | 증인과 성질 분리 |
| `h.exists` | ∃! → ∃ | 유일존재에서 존재 |
| `h.unique` | 두 증인 같음 | `h.unique ha hb` |

### 전수 증명 전술

| 전술 | 용도 | 예시 |
|-----|------|------|
| `decide` | 결정가능 명제 자동 증명 | `example : 2 + 2 = 4 := by decide` |
| `native_decide` | 큰 계산 자동 증명 | `example : 100! > 0 := by native_decide` |

### 추론 방향 전술

| 전술 | 방향 | 용도 |
|-----|------|------|
| `have h := ...` | 전향 | 중간 결과 도입 |
| `apply h` | 후향 | 목표 단순화 |

---

## 4-5.18 증명 방법 선택 가이드

| 상황 | 추천 방법 |
|------|---------|
| 경우의 수가 적고 유한 | **전수 증명** (decide) |
| 경우로 자연스럽게 분류됨 | **경우에 의한 증명** (cases/rcases) |
| "존재한다"를 증명 | **존재 증명** (use) |
| "유일하게 존재한다"를 증명 | **유일성 증명** (use + 유일성) |
| "모든 x에 대해"가 거짓 | **반례** (use + 부정 증명) |
| 대칭적인 경우들 | **WLOG** (한 경우만 증명) |

---

**(끝)**
