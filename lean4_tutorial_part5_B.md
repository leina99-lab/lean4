# Lean4 완전 정복 가이드 — 제5편 (Part B)

## 기초: 정리 사용과 부등식 증명

> **교재**: Mathematics in Lean, Chapter 2 "Basics"  
> **범위**: 2.3절 Using Theorems and Lemmas, 2.4절 More examples using apply and rw  
> **선수 학습**: Part A (계산, 재작성, 대수적 구조 기초)

---

## 5.9 정리와 보조정리 사용하기

### 5.9.1 정리 적용의 기본 원리

Lean4에서 정리(theorem)나 보조정리(lemma)는 **함수처럼 적용**할 수 있다:

```lean
-- 정리: le_refl (반사성)
#check (le_refl : ∀ a : ℝ, a ≤ a)

-- 정리를 인자에 적용
#check (le_refl 3 : 3 ≤ 3)        -- 구체적인 값
#check (le_refl a : a ≤ a)        -- 변수 (a가 컨텍스트에 있을 때)
```

### 5.9.2 함의(→)가 있는 정리

```lean
-- le_trans: 추이성
#check (le_trans : a ≤ b → b ≤ c → a ≤ c)

-- 가설 h : a ≤ b, h' : b ≤ c가 있을 때:
variable (h : a ≤ b) (h' : b ≤ c)

#check (le_trans h : b ≤ c → a ≤ c)   -- h 적용 후
#check (le_trans h h' : a ≤ c)        -- 두 가설 모두 적용
```

### 5.9.3 암시적 인자(Implicit Arguments)

Lean4에서 `{...}`로 선언된 인자는 **암시적**이어서 생략할 수 있다:

```lean
-- le_trans의 실제 타입
-- le_trans : ∀ {a b c : ℝ}, a ≤ b → b ≤ c → a ≤ c
--            ^^^^^^^^^^^^^
--            암시적 인자 (자동 추론)

-- 따라서 le_trans h h'만 쓰면 a, b, c는 자동 추론됨
example (a b c : ℝ) (h : a ≤ b) (h' : b ≤ c) : a ≤ c :=
  le_trans h h'
```

---

## 5.10 apply 전술

### 5.10.1 apply란?

`apply` 전술은 **정리의 결론을 목표에 매칭**하고, 전제를 새 목표로 만든다:

```lean
-- apply h : h의 결론이 현재 목표와 매칭되면
--           h의 전제들이 새 목표가 됨

example (a b c : ℝ) (h₀ : a ≤ b) (h₁ : b ≤ c) : a ≤ c := by
  apply le_trans   -- le_trans의 결론 "a ≤ c"가 목표와 매칭
  -- 새 목표 1: a ≤ ?b (어떤 중간값)
  -- 새 목표 2: ?b ≤ c
  · exact h₀       -- 첫 번째 목표 해결
  · exact h₁       -- 두 번째 목표 해결
```

### 5.10.2 apply의 동작 과정

```
목표: a ≤ c
↓ apply le_trans
목표 1: a ≤ ?m  (중간값 ?m을 찾아야 함)
목표 2: ?m ≤ c
↓ exact h₀ (h₀ : a ≤ b를 제공하면 ?m = b로 결정)
목표: b ≤ c
↓ exact h₁
완료!
```

### 5.10.3 apply vs exact

| 전술 | 용도 | 새 목표 생성 |
|-----|------|------------|
| `exact h` | h가 목표와 **정확히** 일치 | 없음 |
| `apply h` | h의 **결론**이 목표와 매칭 | 전제들이 새 목표가 됨 |

```lean
-- exact 사용
example (a : ℝ) : a ≤ a := by
  exact le_refl a    -- le_refl a : a ≤ a가 목표와 정확히 일치

-- apply 사용 (이 경우도 동작)
example (a : ℝ) : a ≤ a := by
  apply le_refl      -- le_refl의 결론이 a ≤ a이므로 매칭, 새 목표 없음
```

---

### 5.10.4 연습문제 7: apply와 exact

#### 연습 7-1: 추이성 사용
```lean
-- h₀ : a ≤ b, h₁ : b < c, h₂ : c ≤ d, h₃ : d < e일 때 a < e 증명
-- 힌트: lt_of_le_of_lt, lt_of_lt_of_le, lt_trans 사용

#check (lt_of_le_of_lt : a ≤ b → b < c → a < c)
#check (lt_of_lt_of_le : a < b → b ≤ c → a < c)
#check (lt_trans : a < b → b < c → a < c)

example (a b c d e : ℝ) (h₀ : a ≤ b) (h₁ : b < c) (h₂ : c ≤ d) (h₃ : d < e) : 
    a < e := by
  sorry
```

<details>
<summary> 답 보기</summary>

```lean
example (a b c d e : ℝ) (h₀ : a ≤ b) (h₁ : b < c) (h₂ : c ≤ d) (h₃ : d < e) : 
    a < e := by
  -- a < c 먼저
  have hac : a < c := lt_of_le_of_lt h₀ h₁
  -- c < e 다음
  have hce : c < e := lt_of_lt_of_le (lt_of_le_of_lt h₂ h₃) (le_refl e)
  -- 아, 다시:
  -- c ≤ d, d < e → c < e
  have hce : c < e := lt_of_le_of_lt h₂ h₃
  -- a < c, c < e → a < e
  exact lt_trans hac hce
```

또는 apply 체인으로:
```lean
example (a b c d e : ℝ) (h₀ : a ≤ b) (h₁ : b < c) (h₂ : c ≤ d) (h₃ : d < e) : 
    a < e := by
  apply lt_trans
  · apply lt_of_le_of_lt h₀ h₁
  · apply lt_of_le_of_lt h₂ h₃
```

</details>

#### 연습 7-2: 반사성
```lean
example (a : ℝ) : a ≤ a := by
  sorry
```

<details>
<summary> 답 보기</summary>

```lean
example (a : ℝ) : a ≤ a := by
  exact le_refl a
  -- 또는: apply le_refl
  -- 또는: rfl  (일부 경우)
```

</details>

---

## 5.11 linarith 전술

### 5.11.1 linarith란?

`linarith`(linear arithmetic)는 **선형 부등식과 등식**을 자동으로 증명한다:

```lean
-- linarith는 다음을 자동 처리:
-- - 선형 부등식 조합
-- - 덧셈, 뺄셈, 상수 곱셈
-- - 컨텍스트의 가설들을 자동 사용

example (a b c d : ℝ) (h : a ≤ b) (h' : c ≤ d) : a + c ≤ b + d := by
  linarith

example (x : ℝ) (h : x ≥ 0) : x + 1 ≥ 1 := by
  linarith

example (a b : ℝ) (h : 2 * a ≤ 3 * b) (h' : 1 ≤ a) (h'' : d = 2) : 
    d + a ≤ 5 * b := by
  linarith
```

### 5.11.2 linarith에 추가 가설 제공

`linarith [h₁, h₂, ...]`로 추가 사실을 제공할 수 있다:

```lean
-- exp_le_exp.mpr : a ≤ b → exp a ≤ exp b
#check (exp_le_exp.mpr : a ≤ b → Real.exp a ≤ Real.exp b)

example (a b c : ℝ) (h : 1 ≤ a) (h' : b ≤ c) : 
    2 + a + Real.exp b ≤ 3 * a + Real.exp c := by
  linarith [Real.exp_le_exp.mpr h']
  -- exp b ≤ exp c를 linarith에 알려줌
```

### 5.11.3 linarith의 한계

`linarith`는 **선형** 산술만 처리한다:
- ✓ `a + b`, `a - b`, `2 * a`
- ✗ `a * b` (두 변수의 곱)
- ✗ `a ^ 2`, `a / b`

```lean
-- 이것은 안 됨:
-- example (a b : ℝ) (h : a ≥ 0) (h' : b ≥ 0) : a * b ≥ 0 := by linarith
-- 대신 mul_nonneg 같은 정리 필요
```

---

### 5.11.4 연습문제 8: linarith 사용

#### 연습 8-1: 단순 부등식
```lean
example (a b c : ℝ) (h : a ≤ b) : a + c ≤ b + c := by
  sorry
```

<details>
<summary> 답 보기</summary>

```lean
example (a b c : ℝ) (h : a ≤ b) : a + c ≤ b + c := by
  linarith
```

</details>

#### 연습 8-2: 여러 가설 조합
```lean
example (a b c : ℝ) (h₁ : a ≤ b) (h₂ : b ≤ c) (h₃ : c ≤ 10) : a ≤ 10 := by
  sorry
```

<details>
<summary> 답 보기</summary>

```lean
example (a b c : ℝ) (h₁ : a ≤ b) (h₂ : b ≤ c) (h₃ : c ≤ 10) : a ≤ 10 := by
  linarith
```

</details>

#### 연습 8-3: 구체적 수치
```lean
example : (0 : ℝ) < 1 := by
  sorry
```

<details>
<summary> 답 보기</summary>

```lean
example : (0 : ℝ) < 1 := by
  norm_num
  -- 또는: linarith (일부 경우)
```

</details>

---

## 5.12 부등식 정리들

### 5.12.1 기본 부등식 정리

```lean
-- 반사성과 추이성
#check (le_refl : ∀ a : ℝ, a ≤ a)
#check (le_trans : a ≤ b → b ≤ c → a ≤ c)
#check (lt_trans : a < b → b < c → a < c)

-- 혼합 추이성
#check (lt_of_le_of_lt : a ≤ b → b < c → a < c)
#check (lt_of_lt_of_le : a < b → b ≤ c → a < c)
```

### 5.12.2 덧셈 관련 부등식

```lean
-- 양변에 같은 것을 더함
#check (add_le_add : a ≤ b → c ≤ d → a + c ≤ b + d)
#check (add_le_add_left : a ≤ b → ∀ c, c + a ≤ c + b)
#check (add_le_add_right : a ≤ b → ∀ c, a + c ≤ b + c)

-- 엄격한 부등식 버전
#check (add_lt_add_left : a < b → ∀ c, c + a < c + b)
#check (add_lt_add_right : a < b → ∀ c, a + c < b + c)
#check (add_lt_add_of_le_of_lt : a ≤ b → c < d → a + c < b + d)
#check (add_lt_add_of_lt_of_le : a < b → c ≤ d → a + c < b + d)
```

### 5.12.3 양수/음이 아닌 수

```lean
-- 0과의 비교
#check (add_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a + b)
#check (add_pos : 0 < a → 0 < b → 0 < a + b)
#check (add_pos_of_pos_of_nonneg : 0 < a → 0 ≤ b → 0 < a + b)

-- 지수함수는 항상 양수
#check (Real.exp_pos : ∀ a, 0 < Real.exp a)
```

### 5.12.4 쌍조건문 정리와 .mpr

```lean
-- 쌍조건문 (↔) 정리
#check (Real.exp_le_exp : Real.exp a ≤ Real.exp b ↔ a ≤ b)
#check (Real.exp_lt_exp : Real.exp a < Real.exp b ↔ a < b)

-- .mp : 정방향 (왼쪽 → 오른쪽)
-- .mpr : 역방향 (오른쪽 → 왼쪽)

-- exp a ≤ exp b ↔ a ≤ b에서:
-- exp_le_exp.mp  : exp a ≤ exp b → a ≤ b
-- exp_le_exp.mpr : a ≤ b → exp a ≤ exp b

example (h : a ≤ b) : Real.exp a ≤ Real.exp b := by
  exact Real.exp_le_exp.mpr h
```

---

### 5.12.5 연습문제 9: 부등식 증명

#### 연습 9-1: 덧셈 부등식
```lean
example (a b c d : ℝ) (h₀ : a ≤ b) (h₁ : c < d) : a + c < b + d := by
  sorry
```

<details>
<summary> 답 보기</summary>

```lean
example (a b c d : ℝ) (h₀ : a ≤ b) (h₁ : c < d) : a + c < b + d := by
  apply add_lt_add_of_le_of_lt h₀ h₁
  -- 또는: linarith
```

</details>

#### 연습 9-2: 지수함수 부등식
```lean
example (h₀ : d ≤ e) : c + Real.exp (a + d) ≤ c + Real.exp (a + e) := by
  sorry
```

<details>
<summary> 답 보기</summary>

```lean
example (h₀ : d ≤ e) : c + Real.exp (a + d) ≤ c + Real.exp (a + e) := by
  apply add_le_add_left
  apply Real.exp_le_exp.mpr
  linarith
```

</details>

#### 연습 9-3: 로그 부등식
```lean
-- log_le_log : 0 < a → a ≤ b → log a ≤ log b

example (h : a ≤ b) : Real.log (1 + Real.exp a) ≤ Real.log (1 + Real.exp b) := by
  have h₀ : 0 < 1 + Real.exp a := by
    sorry  -- 먼저 이것을 증명
  sorry
```

<details>
<summary> 답 보기</summary>

```lean
example (h : a ≤ b) : Real.log (1 + Real.exp a) ≤ Real.log (1 + Real.exp b) := by
  have h₀ : 0 < 1 + Real.exp a := by
    have : 0 < Real.exp a := Real.exp_pos a
    linarith
  apply Real.log_le_log h₀
  apply add_le_add_left
  exact Real.exp_le_exp.mpr h
```

</details>

---

## 5.13 쌍조건문(↔)과 재작성

### 5.13.1 ↔를 rw에 사용

쌍조건문 `A ↔ B`는 `rw`에 직접 사용할 수 있다:

```lean
-- exp_le_exp : exp a ≤ exp b ↔ a ≤ b

example (h : a ≤ b) : Real.exp a ≤ Real.exp b := by
  rw [Real.exp_le_exp]  -- 목표가 exp a ≤ exp b에서 a ≤ b로 변환
  exact h
```

### 5.13.2 .mp와 .mpr

| 표기 | 의미 | 방향 |
|-----|------|------|
| `h.mp` | modus ponens | A → B |
| `h.mpr` | modus ponens reverse | B → A |
| `h.1` | `h.mp`와 동일 | A → B |
| `h.2` | `h.mpr`와 동일 | B → A |

```lean
-- h : A ↔ B일 때
-- h.mp  : A → B
-- h.mpr : B → A

example (h : a ≤ b) : Real.exp a ≤ Real.exp b :=
  Real.exp_le_exp.mpr h   -- a ≤ b → exp a ≤ exp b
```

---

## 5.14 군(Group)의 기본 정리

### 5.14.1 군이란?

**군**(Group)은 환보다 약한 구조로, 곱셈(또는 덧셈)만 있다:

**가법군**(Additive Group) 공리:
```lean
variable (A : Type*) [AddGroup A]

#check (add_assoc : ∀ a b c : A, a + b + c = a + (b + c))
#check (zero_add : ∀ a : A, 0 + a = a)
#check (neg_add_cancel : ∀ a : A, -a + a = 0)
```

**승법군**(Multiplicative Group) 공리:
```lean
variable (G : Type*) [Group G]

#check (mul_assoc : ∀ a b c : G, a * b * c = a * (b * c))
#check (one_mul : ∀ a : G, 1 * a = a)
#check (inv_mul_cancel : ∀ a : G, a⁻¹ * a = 1)
```

### 5.14.2 군에서 증명할 정리들

```lean
-- 다음은 공리가 아니라 공리에서 유도됨:

-- mul_one : a * 1 = a
-- mul_inv_cancel : a * a⁻¹ = 1
-- mul_inv_rev : (a * b)⁻¹ = b⁻¹ * a⁻¹
```

---

### 5.14.3 연습문제 10: 군 정리 증명

#### 연습 10-1: mul_inv_cancel
```lean
-- a * a⁻¹ = 1을 증명하라
-- 힌트: 환에서 했던 것처럼 have로 보조 사실 도입

theorem my_mul_inv_cancel (G : Type*) [Group G] (a : G) : a * a⁻¹ = 1 := by
  sorry
```

<details>
<summary> 답 보기</summary>

```lean
theorem my_mul_inv_cancel (G : Type*) [Group G] (a : G) : a * a⁻¹ = 1 := by
  -- 핵심: a⁻¹ * (a * a⁻¹) = a⁻¹ * 1을 보이고 cancel
  have h : a⁻¹ * (a * a⁻¹) = a⁻¹ * 1 := by
    rw [← mul_assoc]      -- a⁻¹ * (a * a⁻¹) → a⁻¹ * a * a⁻¹
    rw [inv_mul_cancel]   -- a⁻¹ * a * a⁻¹ → 1 * a⁻¹
    rw [one_mul]          -- 1 * a⁻¹ → a⁻¹
    rw [mul_one]          -- a⁻¹ * 1 → a⁻¹
  -- 이제 양변에서 a⁻¹을 소거
  -- 실제로는 더 정교한 방법 필요
  calc a * a⁻¹ = 1 * (a * a⁻¹) := by rw [one_mul]
             _ = (a⁻¹⁻¹ * a⁻¹) * (a * a⁻¹) := by rw [inv_mul_cancel]
             _ = a⁻¹⁻¹ * (a⁻¹ * (a * a⁻¹)) := by rw [mul_assoc, mul_assoc]
             _ = a⁻¹⁻¹ * (a⁻¹ * a * a⁻¹) := by rw [← mul_assoc a⁻¹ a a⁻¹]
             _ = a⁻¹⁻¹ * (1 * a⁻¹) := by rw [inv_mul_cancel]
             _ = a⁻¹⁻¹ * a⁻¹ := by rw [one_mul]
             _ = 1 := by rw [inv_mul_cancel]
```

**더 간단한 방법** (Mathlib 스타일):
```lean
theorem my_mul_inv_cancel' (G : Type*) [Group G] (a : G) : a * a⁻¹ = 1 := by
  group  -- group 전술이 자동 처리
```

</details>

#### 연습 10-2: mul_one
```lean
-- a * 1 = a를 증명하라

theorem my_mul_one (G : Type*) [Group G] (a : G) : a * 1 = a := by
  sorry
```

<details>
<summary> 답 보기</summary>

```lean
theorem my_mul_one (G : Type*) [Group G] (a : G) : a * 1 = a := by
  calc a * 1 = a * (a⁻¹ * a) := by rw [inv_mul_cancel]
           _ = (a * a⁻¹) * a := by rw [mul_assoc]
           _ = 1 * a := by rw [my_mul_inv_cancel]  -- 또는 mul_inv_cancel
           _ = a := by rw [one_mul]
```

</details>

#### 연습 10-3: mul_inv_rev
```lean
-- (a * b)⁻¹ = b⁻¹ * a⁻¹를 증명하라

theorem my_mul_inv_rev (G : Type*) [Group G] (a b : G) : 
    (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  sorry
```

<details>
<summary> 답 보기</summary>

```lean
theorem my_mul_inv_rev (G : Type*) [Group G] (a b : G) : 
    (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  -- x * (a * b) = 1이면 x = (a * b)⁻¹
  -- b⁻¹ * a⁻¹ * (a * b) = 1을 보이면 됨
  have h : (b⁻¹ * a⁻¹) * (a * b) = 1 := by
    calc (b⁻¹ * a⁻¹) * (a * b) 
        = b⁻¹ * (a⁻¹ * (a * b)) := by rw [mul_assoc]
      _ = b⁻¹ * ((a⁻¹ * a) * b) := by rw [← mul_assoc a⁻¹ a b]
      _ = b⁻¹ * (1 * b) := by rw [inv_mul_cancel]
      _ = b⁻¹ * b := by rw [one_mul]
      _ = 1 := by rw [inv_mul_cancel]
  -- (a * b)⁻¹ * (a * b) = 1도 성립
  -- 양변에 (a * b)를 곱하고 소거
  calc (a * b)⁻¹ = (a * b)⁻¹ * 1 := by rw [mul_one]
               _ = (a * b)⁻¹ * ((a * b) * ((a * b)⁻¹)) := by rw [mul_inv_cancel]
               -- 복잡해지므로 다른 방법 시도
  sorry  -- 실제로는 group 전술 사용 권장
```

**Mathlib 스타일**:
```lean
theorem my_mul_inv_rev' (G : Type*) [Group G] (a b : G) : 
    (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  group
```

</details>

---

## 5.15 자동화 전술들

### 5.15.1 ring

**환**(Ring)의 등식을 자동 증명:

```lean
example (a b c : ℝ) : (a + b) * c = a * c + b * c := by ring
example (a b : ℝ) : (a + b)^2 = a^2 + 2*a*b + b^2 := by ring
```

### 5.15.2 group

**군**(Group)의 등식을 자동 증명:

```lean
example (G : Type*) [Group G] (a b : G) : a * b * b⁻¹ = a := by group
example (G : Type*) [Group G] (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by group
```

### 5.15.3 abel

**아벨군**(Abelian Group, 가환군)의 등식을 자동 증명:

```lean
example (A : Type*) [AddCommGroup A] (a b c : A) : a + b + c = c + b + a := by abel
```

### 5.15.4 norm_num

**구체적인 수치 계산**을 자동 증명:

```lean
example : (2 : ℝ) + 3 = 5 := by norm_num
example : (10 : ℕ) > 5 := by norm_num
example : (7 : ℤ) ≠ 3 := by norm_num
```

### 5.15.5 linarith

**선형 부등식/등식**을 자동 증명:

```lean
example (a b : ℝ) (h : a < b) : a + 1 < b + 1 := by linarith
example (a b c : ℝ) (h₁ : a ≤ b) (h₂ : b ≤ c) : a ≤ c := by linarith
```

---

## 5.16 종합 연습문제

### 연습 11-1: calc 종합
```lean
-- (x + y)³ = x³ + 3x²y + 3xy² + y³

example (x y : ℝ) : (x + y)^3 = x^3 + 3*x^2*y + 3*x*y^2 + y^3 := by
  sorry
```

<details>
<summary> 답 보기</summary>

```lean
example (x y : ℝ) : (x + y)^3 = x^3 + 3*x^2*y + 3*x*y^2 + y^3 := by
  ring
```

</details>

### 연습 11-2: 부등식 연쇄
```lean
example (a b c d : ℝ) (h₁ : a ≤ b) (h₂ : c ≤ d) (h₃ : 0 ≤ a) (h₄ : 0 ≤ c) :
    a * c ≤ b * d := by
  sorry
```

<details>
<summary> 답 보기</summary>

```lean
example (a b c d : ℝ) (h₁ : a ≤ b) (h₂ : c ≤ d) (h₃ : 0 ≤ a) (h₄ : 0 ≤ c) :
    a * c ≤ b * d := by
  -- a * c ≤ b * c ≤ b * d
  have h5 : a * c ≤ b * c := by
    apply mul_le_mul_of_nonneg_right h₁ h₄
  have h6 : b * c ≤ b * d := by
    apply mul_le_mul_of_nonneg_left h₂
    linarith
  linarith
```

</details>

### 연습 11-3: 혼합 증명
```lean
example (a b : ℝ) (h : a = b + 1) : a^2 = b^2 + 2*b + 1 := by
  sorry
```

<details>
<summary> 답 보기</summary>

```lean
example (a b : ℝ) (h : a = b + 1) : a^2 = b^2 + 2*b + 1 := by
  rw [h]
  ring
```

</details>

---

## 5.17 전술 요약표

### 재작성 전술

| 전술 | 용도 | 예시 |
|-----|------|------|
| `rw [h]` | h의 좌변→우변 치환 | `rw [mul_comm]` |
| `rw [← h]` | h의 우변→좌변 치환 | `rw [← mul_assoc]` |
| `rw [h] at hyp` | 가설 hyp에서 재작성 | `rw [h'] at h` |
| `nth_rw n [h]` | n번째 매칭만 재작성 | `nth_rw 2 [h]` |

### 적용 전술

| 전술 | 용도 | 예시 |
|-----|------|------|
| `exact h` | 목표와 정확히 일치 | `exact le_refl a` |
| `apply h` | 결론 매칭, 전제가 새 목표 | `apply le_trans` |

### 자동화 전술

| 전술 | 용도 |
|-----|------|
| `ring` | 환의 등식 |
| `group` | 군의 등식 |
| `abel` | 아벨군의 등식 |
| `linarith` | 선형 산술 |
| `norm_num` | 수치 계산 |

### 구조화 전술

| 전술 | 용도 |
|-----|------|
| `have h : P := by ...` | 보조 사실 도입 |
| `calc ... := by ...` | 단계별 계산 |

---

**(끝)**
