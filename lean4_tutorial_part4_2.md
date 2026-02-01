# Lean4 완전 정복 가이드 — 제4-2편

## 명제 논리의 응용과 논리적 동치

---

# 제4-2편: 논리적 동치와 증명 실전

---

## 4-2.1 이 장의 목표

이 장에서는 **논리적 동치**(Logical Equivalence)를 Lean4로 증명하는 방법을 배운다.

**배울 내용:**
- 항진명제(tautology)와 모순(contradiction)
- 논리적 동치의 정의와 증명
- 드 모르간 법칙(De Morgan's Laws)
- 조건문을 포함한 논리적 동치
- 시스템 명세의 일관성 검증

**전제 조건:**
- 3편(명제와 증명)을 먼저 학습할 것
- 4편(치환과 계산)을 먼저 학습할 것
- 4-1편(명제 논리 완전 정복)을 먼저 학습할 것

---

## 4-2.2 핵심 개념 정리

### 항진명제(Tautology)란?

**항진명제**(tautology)는 명제 변수가 어떤 진리값을 가지더라도 **항상 참**인 복합명제이다.

**예시:**
\`\`\`
p ∨ ¬p  (배중률)
→ p가 참이면: T ∨ F = T
→ p가 거짓이면: F ∨ T = T
→ 항상 참! ∴ 항진명제
\`\`\`

### 모순(Contradiction)이란?

**모순**(contradiction)은 명제 변수가 어떤 진리값을 가지더라도 **항상 거짓**인 복합명제이다.

**예시:**
\`\`\`
p ∧ ¬p  (모순)
→ p가 참이면: T ∧ F = F
→ p가 거짓이면: F ∧ T = F
→ 항상 거짓! ∴ 모순
\`\`\`

### 논리적 동치(Logical Equivalence)란?

두 복합명제 p, q에 대하여, \`p ↔ q\`가 항진명제이면, **p와 q는 논리적 동치**이다.

**기호:** \`p ≡ q\` (교재) 또는 \`p ↔ q\` (Lean4)

**의미:** 모든 경우에 p와 q의 진리값이 같다.

---

## 4-2.3 Lean4에서 논리적 동치

Lean4에서 **논리적 동치**는 \`↔\` (if and only if, iff)로 표현한다.

\`\`\`lean
-- p ↔ q 는 "p이면 q이고, q이면 p이다"와 같다
-- 즉, (p → q) ∧ (q → p)

example (p q : Prop) : (p ↔ q) ↔ ((p → q) ∧ (q → p)) := by
  constructor
  · intro h
    constructor
    · exact h.mp      -- p ↔ q에서 p → q 추출
    · exact h.mpr     -- p ↔ q에서 q → p 추출
  · intro ⟨hpq, hqp⟩
    exact ⟨hpq, hqp⟩  -- (p → q) ∧ (q → p)로 p ↔ q 구성
\`\`\`

### ↔의 두 가지 방향

\`\`\`lean
-- h : p ↔ q 일 때
-- h.mp  : p → q  (mp = modus ponens, 정방향)
-- h.mpr : q → p  (mpr = modus ponens reverse, 역방향)

example (p q : Prop) (h : p ↔ q) (hp : p) : q := by
  exact h.mp hp   -- h.mp : p → q, hp : p, 따라서 q

example (p q : Prop) (h : p ↔ q) (hq : q) : p := by
  exact h.mpr hq  -- h.mpr : q → p, hq : q, 따라서 p
\`\`\`

---

## 4-2.4 표 6: 핵심 논리적 동치 (Lean4 버전)

교재의 **표 6 논리적 동치**를 Lean4로 정리한다.

### 항등 법칙(Identity Laws)

\`\`\`
p ∧ True ≡ p
p ∨ False ≡ p
\`\`\`

\`\`\`lean
-- 항등 법칙 1: p ∧ True ↔ p
theorem identity_and (p : Prop) : (p ∧ True) ↔ p := by
  constructor
  · intro ⟨hp, _⟩    -- p ∧ True에서 p 추출
    exact hp
  · intro hp
    exact ⟨hp, trivial⟩  -- p와 True로 p ∧ True 구성

-- 항등 법칙 2: p ∨ False ↔ p
theorem identity_or (p : Prop) : (p ∨ False) ↔ p := by
  constructor
  · intro h
    cases h with
    | inl hp => exact hp
    | inr hf => exact False.elim hf
  · intro hp
    exact Or.inl hp
\`\`\`

### 지배 법칙(Domination Laws)

\`\`\`
p ∨ True ≡ True
p ∧ False ≡ False
\`\`\`

\`\`\`lean
-- 지배 법칙 1: p ∨ True ↔ True
theorem domination_or (p : Prop) : (p ∨ True) ↔ True := by
  constructor
  · intro _
    trivial
  · intro _
    exact Or.inr trivial

-- 지배 법칙 2: p ∧ False ↔ False
theorem domination_and (p : Prop) : (p ∧ False) ↔ False := by
  constructor
  · intro ⟨_, hf⟩
    exact hf
  · intro hf
    exact False.elim hf
\`\`\`

### 등멱 법칙(Idempotent Laws)

\`\`\`
p ∨ p ≡ p
p ∧ p ≡ p
\`\`\`

\`\`\`lean
-- 등멱 법칙 1: p ∨ p ↔ p
theorem idempotent_or (p : Prop) : (p ∨ p) ↔ p := by
  constructor
  · intro h
    cases h with
    | inl hp => exact hp
    | inr hp => exact hp
  · intro hp
    exact Or.inl hp

-- 등멱 법칙 2: p ∧ p ↔ p
theorem idempotent_and (p : Prop) : (p ∧ p) ↔ p := by
  constructor
  · intro ⟨hp, _⟩
    exact hp
  · intro hp
    exact ⟨hp, hp⟩
\`\`\`

### 이중 부정 법칙(Double Negation)

\`\`\`
¬(¬p) ≡ p
\`\`\`

\`\`\`lean
-- 이중 부정 법칙: ¬¬p ↔ p (고전 논리 필요)
theorem double_negation (p : Prop) : ¬¬p ↔ p := by
  constructor
  · intro hnnp
    by_contra hnp    -- 귀류법: ¬p를 가정
    exact hnnp hnp   -- hnnp : ¬¬p, hnp : ¬p → 모순
  · intro hp hnp
    exact hnp hp     -- hp : p, hnp : ¬p → 모순
\`\`\`

### 교환 법칙(Commutative Laws)

\`\`\`
p ∨ q ≡ q ∨ p
p ∧ q ≡ q ∧ p
\`\`\`

\`\`\`lean
-- 교환 법칙 1: p ∨ q ↔ q ∨ p
theorem comm_or (p q : Prop) : (p ∨ q) ↔ (q ∨ p) := by
  constructor
  · intro h
    cases h with
    | inl hp => exact Or.inr hp
    | inr hq => exact Or.inl hq
  · intro h
    cases h with
    | inl hq => exact Or.inr hq
    | inr hp => exact Or.inl hp

-- 교환 법칙 2: p ∧ q ↔ q ∧ p
theorem comm_and (p q : Prop) : (p ∧ q) ↔ (q ∧ p) := by
  constructor
  · intro ⟨hp, hq⟩
    exact ⟨hq, hp⟩
  · intro ⟨hq, hp⟩
    exact ⟨hp, hq⟩
\`\`\`

### 결합 법칙(Associative Laws)

\`\`\`
(p ∨ q) ∨ r ≡ p ∨ (q ∨ r)
(p ∧ q) ∧ r ≡ p ∧ (q ∧ r)
\`\`\`

\`\`\`lean
-- 결합 법칙 1: (p ∨ q) ∨ r ↔ p ∨ (q ∨ r)
theorem assoc_or (p q r : Prop) : ((p ∨ q) ∨ r) ↔ (p ∨ (q ∨ r)) := by
  constructor
  · intro h
    cases h with
    | inl hpq =>
      cases hpq with
      | inl hp => exact Or.inl hp
      | inr hq => exact Or.inr (Or.inl hq)
    | inr hr => exact Or.inr (Or.inr hr)
  · intro h
    cases h with
    | inl hp => exact Or.inl (Or.inl hp)
    | inr hqr =>
      cases hqr with
      | inl hq => exact Or.inl (Or.inr hq)
      | inr hr => exact Or.inr hr

-- 결합 법칙 2: (p ∧ q) ∧ r ↔ p ∧ (q ∧ r)
theorem assoc_and (p q r : Prop) : ((p ∧ q) ∧ r) ↔ (p ∧ (q ∧ r)) := by
  constructor
  · intro ⟨⟨hp, hq⟩, hr⟩
    exact ⟨hp, hq, hr⟩
  · intro ⟨hp, hq, hr⟩
    exact ⟨⟨hp, hq⟩, hr⟩
\`\`\`

---

## 4-2.5 분배 법칙(Distributive Laws)

\`\`\`
p ∨ (q ∧ r) ≡ (p ∨ q) ∧ (p ∨ r)
p ∧ (q ∨ r) ≡ (p ∧ q) ∨ (p ∧ r)
\`\`\`

### 분배 법칙 1: ∨가 ∧에 분배

\`\`\`lean
-- p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r)
theorem dist_or_and (p q r : Prop) : (p ∨ (q ∧ r)) ↔ ((p ∨ q) ∧ (p ∨ r)) := by
  constructor
  -- 정방향: p ∨ (q ∧ r) → (p ∨ q) ∧ (p ∨ r)
  · intro h
    cases h with
    | inl hp =>
      constructor
      · exact Or.inl hp
      · exact Or.inl hp
    | inr hqr =>
      obtain ⟨hq, hr⟩ := hqr
      constructor
      · exact Or.inr hq
      · exact Or.inr hr
  -- 역방향: (p ∨ q) ∧ (p ∨ r) → p ∨ (q ∧ r)
  · intro ⟨hpq, hpr⟩
    cases hpq with
    | inl hp => exact Or.inl hp
    | inr hq =>
      cases hpr with
      | inl hp => exact Or.inl hp
      | inr hr => exact Or.inr ⟨hq, hr⟩
\`\`\`

### 분배 법칙 2: ∧가 ∨에 분배

\`\`\`lean
-- p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r)
theorem dist_and_or (p q r : Prop) : (p ∧ (q ∨ r)) ↔ ((p ∧ q) ∨ (p ∧ r)) := by
  constructor
  · intro ⟨hp, hqr⟩
    cases hqr with
    | inl hq => exact Or.inl ⟨hp, hq⟩
    | inr hr => exact Or.inr ⟨hp, hr⟩
  · intro h
    cases h with
    | inl hpq =>
      obtain ⟨hp, hq⟩ := hpq
      exact ⟨hp, Or.inl hq⟩
    | inr hpr =>
      obtain ⟨hp, hr⟩ := hpr
      exact ⟨hp, Or.inr hr⟩
\`\`\`

---

## 4-2.6 드 모르간 법칙(De Morgan's Laws)

**드 모르간 법칙**은 논리학에서 가장 중요한 동치 중 하나이다.

\`\`\`
¬(p ∧ q) ≡ ¬p ∨ ¬q  (제1 드 모르간 법칙)
¬(p ∨ q) ≡ ¬p ∧ ¬q  (제2 드 모르간 법칙)
\`\`\`

**직관적 이해:**
- "둘 다 참이 **아니다**" = "적어도 하나는 거짓이다"
- "적어도 하나가 참이 **아니다**" = "둘 다 거짓이다"

### 제1 드 모르간 법칙

\`\`\`lean
-- ¬(p ∧ q) ↔ ¬p ∨ ¬q
theorem de_morgan_and (p q : Prop) : ¬(p ∧ q) ↔ (¬p ∨ ¬q) := by
  constructor
  -- 정방향: ¬(p ∧ q) → ¬p ∨ ¬q (고전 논리 필요)
  · intro h
    by_cases hp : p
    · right
      intro hq
      exact h ⟨hp, hq⟩
    · left
      exact hp
  -- 역방향: ¬p ∨ ¬q → ¬(p ∧ q)
  · intro h ⟨hp, hq⟩
    cases h with
    | inl hnp => exact hnp hp
    | inr hnq => exact hnq hq
\`\`\`

### 제2 드 모르간 법칙

\`\`\`lean
-- ¬(p ∨ q) ↔ ¬p ∧ ¬q
theorem de_morgan_or (p q : Prop) : ¬(p ∨ q) ↔ (¬p ∧ ¬q) := by
  constructor
  · intro h
    constructor
    · intro hp
      exact h (Or.inl hp)
    · intro hq
      exact h (Or.inr hq)
  · intro ⟨hnp, hnq⟩ hpq
    cases hpq with
    | inl hp => exact hnp hp
    | inr hq => exact hnq hq
\`\`\`

---

## 4-2.7 흡수 법칙(Absorption Laws)

\`\`\`
p ∨ (p ∧ q) ≡ p
p ∧ (p ∨ q) ≡ p
\`\`\`

\`\`\`lean
-- 흡수 법칙 1: p ∨ (p ∧ q) ↔ p
theorem absorption_or (p q : Prop) : (p ∨ (p ∧ q)) ↔ p := by
  constructor
  · intro h
    cases h with
    | inl hp => exact hp
    | inr hpq => exact hpq.1
  · intro hp
    exact Or.inl hp

-- 흡수 법칙 2: p ∧ (p ∨ q) ↔ p
theorem absorption_and (p q : Prop) : (p ∧ (p ∨ q)) ↔ p := by
  constructor
  · intro ⟨hp, _⟩
    exact hp
  · intro hp
    exact ⟨hp, Or.inl hp⟩
\`\`\`

---

## 4-2.8 부정 법칙(Negation Laws)

\`\`\`
p ∨ ¬p ≡ True   (배중률, Excluded Middle)
p ∧ ¬p ≡ False  (모순)
\`\`\`

\`\`\`lean
-- 배중률: p ∨ ¬p ↔ True
theorem excluded_middle_equiv (p : Prop) : (p ∨ ¬p) ↔ True := by
  constructor
  · intro _
    trivial
  · intro _
    exact Classical.em p

-- 모순: p ∧ ¬p ↔ False
theorem contradiction_equiv (p : Prop) : (p ∧ ¬p) ↔ False := by
  constructor
  · intro ⟨hp, hnp⟩
    exact hnp hp
  · intro hf
    exact False.elim hf
\`\`\`

---

## 4-2.9 조건문을 포함한 논리적 동치 (표 7)

### 조건-논리합 동치

\`\`\`
p → q ≡ ¬p ∨ q
\`\`\`

\`\`\`lean
-- p → q ↔ ¬p ∨ q
theorem impl_iff_not_or (p q : Prop) : (p → q) ↔ (¬p ∨ q) := by
  constructor
  · intro h
    by_cases hp : p
    · exact Or.inr (h hp)
    · exact Or.inl hp
  · intro h hp
    cases h with
    | inl hnp => exact False.elim (hnp hp)
    | inr hq => exact hq
\`\`\`

### 대우(Contrapositive)

\`\`\`
p → q ≡ ¬q → ¬p
\`\`\`

\`\`\`lean
-- p → q ↔ ¬q → ¬p
theorem contrapositive (p q : Prop) : (p → q) ↔ (¬q → ¬p) := by
  constructor
  · intro h hnq hp
    exact hnq (h hp)
  · intro h hp
    by_contra hnq
    exact h hnq hp
\`\`\`

### 조건문의 부정

\`\`\`
¬(p → q) ≡ p ∧ ¬q
\`\`\`

\`\`\`lean
-- ¬(p → q) ↔ p ∧ ¬q
theorem not_impl (p q : Prop) : ¬(p → q) ↔ (p ∧ ¬q) := by
  constructor
  · intro h
    constructor
    · by_contra hnp
      apply h
      intro hp
      exact False.elim (hnp hp)
    · intro hq
      apply h
      intro _
      exact hq
  · intro ⟨hp, hnq⟩ hpq
    exact hnq (hpq hp)
\`\`\`

---

## 4-2.10 연습 문제: 항진명제 증명

### 연습 1: 배중률 직접 증명

**문제:** \`p ∨ ¬p\`가 항상 참임을 증명하라.

\`\`\`lean
-- 스켈레톤
theorem em_taut (p : Prop) : p ∨ ¬p := by
  sorry
\`\`\`

<details>
<summary>힌트 보기</summary>

- \`Classical.em p\`를 사용하면 바로 증명 가능
- 또는 \`by_cases hp : p\`로 경우 분류 후 증명

</details>

<details>
<summary>정답 보기</summary>

\`\`\`lean
theorem em_taut (p : Prop) : p ∨ ¬p := by
  exact Classical.em p

-- 또는 직접 증명
theorem em_taut' (p : Prop) : p ∨ ¬p := by
  by_cases hp : p
  · exact Or.inl hp
  · exact Or.inr hp
\`\`\`

</details>

---

### 연습 2: (p ∧ q) → p 증명

**문제:** \`(p ∧ q) → p\`를 증명하라.

\`\`\`lean
-- 스켈레톤
theorem and_elim_left_taut (p q : Prop) : (p ∧ q) → p := by
  sorry
\`\`\`

<details>
<summary>정답 보기</summary>

\`\`\`lean
theorem and_elim_left_taut (p q : Prop) : (p ∧ q) → p := by
  intro h
  exact h.1
\`\`\`

</details>

---

### 연습 3: p → (p ∨ q) 증명

**문제:** \`p → (p ∨ q)\`를 증명하라.

\`\`\`lean
-- 스켈레톤
theorem or_intro_left_taut (p q : Prop) : p → (p ∨ q) := by
  sorry
\`\`\`

<details>
<summary>정답 보기</summary>

\`\`\`lean
theorem or_intro_left_taut (p q : Prop) : p → (p ∨ q) := by
  intro hp
  exact Or.inl hp
\`\`\`

</details>

---

### 연습 4: (p ∧ q) → (p ∨ q) 증명

**문제:** \`(p ∧ q) → (p ∨ q)\`를 증명하라.

\`\`\`lean
-- 스켈레톤
theorem and_implies_or (p q : Prop) : (p ∧ q) → (p ∨ q) := by
  sorry
\`\`\`

<details>
<summary>정답 보기</summary>

\`\`\`lean
theorem and_implies_or (p q : Prop) : (p ∧ q) → (p ∨ q) := by
  intro ⟨hp, _⟩
  exact Or.inl hp
\`\`\`

</details>

---

## 4-2.11 연습 문제: 논리적 동치 증명

### 연습 5: 교환 법칙 (∨)

**문제:** \`p ∨ q ↔ q ∨ p\`를 증명하라.

\`\`\`lean
-- 스켈레톤
theorem or_comm_exercise (p q : Prop) : (p ∨ q) ↔ (q ∨ p) := by
  constructor
  · intro h
    sorry
  · intro h
    sorry
\`\`\`

<details>
<summary>정답 보기</summary>

\`\`\`lean
theorem or_comm_exercise (p q : Prop) : (p ∨ q) ↔ (q ∨ p) := by
  constructor
  · intro h
    cases h with
    | inl hp => exact Or.inr hp
    | inr hq => exact Or.inl hq
  · intro h
    cases h with
    | inl hq => exact Or.inr hq
    | inr hp => exact Or.inl hp
\`\`\`

</details>

---

### 연습 6: 교환 법칙 (∧)

**문제:** \`p ∧ q ↔ q ∧ p\`를 증명하라.

\`\`\`lean
-- 스켈레톤
theorem and_comm_exercise (p q : Prop) : (p ∧ q) ↔ (q ∧ p) := by
  constructor
  · intro h
    sorry
  · intro h
    sorry
\`\`\`

<details>
<summary>정답 보기</summary>

\`\`\`lean
theorem and_comm_exercise (p q : Prop) : (p ∧ q) ↔ (q ∧ p) := by
  constructor
  · intro ⟨hp, hq⟩
    exact ⟨hq, hp⟩
  · intro ⟨hq, hp⟩
    exact ⟨hp, hq⟩
\`\`\`

</details>

---

### 연습 7: 이중 부정

**문제:** \`¬¬p ↔ p\`를 증명하라. (고전 논리 필요)

\`\`\`lean
-- 스켈레톤
theorem double_neg_exercise (p : Prop) : ¬¬p ↔ p := by
  constructor
  · intro hnnp
    sorry
  · intro hp hnp
    sorry
\`\`\`

<details>
<summary>힌트 보기</summary>

- 정방향: \`by_contra\`로 귀류법 사용
- 역방향: \`hnp hp\`로 모순 도출

</details>

<details>
<summary>정답 보기</summary>

\`\`\`lean
theorem double_neg_exercise (p : Prop) : ¬¬p ↔ p := by
  constructor
  · intro hnnp
    by_contra hnp
    exact hnnp hnp
  · intro hp hnp
    exact hnp hp
\`\`\`

</details>

---

### 연습 8: 드 모르간 법칙 (∧)

**문제:** \`¬(p ∧ q) ↔ ¬p ∨ ¬q\`를 증명하라.

\`\`\`lean
-- 스켈레톤
theorem de_morgan_and_exercise (p q : Prop) : ¬(p ∧ q) ↔ (¬p ∨ ¬q) := by
  constructor
  · intro h
    sorry
  · intro h hpq
    sorry
\`\`\`

<details>
<summary>정답 보기</summary>

\`\`\`lean
theorem de_morgan_and_exercise (p q : Prop) : ¬(p ∧ q) ↔ (¬p ∨ ¬q) := by
  constructor
  · intro h
    by_cases hp : p
    · right
      intro hq
      exact h ⟨hp, hq⟩
    · left
      exact hp
  · intro h ⟨hp, hq⟩
    cases h with
    | inl hnp => exact hnp hp
    | inr hnq => exact hnq hq
\`\`\`

</details>

---

### 연습 9: 드 모르간 법칙 (∨)

**문제:** \`¬(p ∨ q) ↔ ¬p ∧ ¬q\`를 증명하라.

\`\`\`lean
-- 스켈레톤
theorem de_morgan_or_exercise (p q : Prop) : ¬(p ∨ q) ↔ (¬p ∧ ¬q) := by
  constructor
  · intro h
    constructor
    · sorry
    · sorry
  · intro ⟨hnp, hnq⟩ hpq
    sorry
\`\`\`

<details>
<summary>정답 보기</summary>

\`\`\`lean
theorem de_morgan_or_exercise (p q : Prop) : ¬(p ∨ q) ↔ (¬p ∧ ¬q) := by
  constructor
  · intro h
    constructor
    · intro hp
      exact h (Or.inl hp)
    · intro hq
      exact h (Or.inr hq)
  · intro ⟨hnp, hnq⟩ hpq
    cases hpq with
    | inl hp => exact hnp hp
    | inr hq => exact hnq hq
\`\`\`

</details>

---

### 연습 10: 조건-논리합 동치

**문제:** \`(p → q) ↔ (¬p ∨ q)\`를 증명하라.

\`\`\`lean
-- 스켈레톤
theorem impl_iff_or_exercise (p q : Prop) : (p → q) ↔ (¬p ∨ q) := by
  constructor
  · intro h
    sorry
  · intro h hp
    sorry
\`\`\`

<details>
<summary>정답 보기</summary>

\`\`\`lean
theorem impl_iff_or_exercise (p q : Prop) : (p → q) ↔ (¬p ∨ q) := by
  constructor
  · intro h
    by_cases hp : p
    · exact Or.inr (h hp)
    · exact Or.inl hp
  · intro h hp
    cases h with
    | inl hnp => exact False.elim (hnp hp)
    | inr hq => exact hq
\`\`\`

</details>

---

### 연습 11: 대우

**문제:** \`(p → q) ↔ (¬q → ¬p)\`를 증명하라.

\`\`\`lean
-- 스켈레톤
theorem contrapos_exercise (p q : Prop) : (p → q) ↔ (¬q → ¬p) := by
  constructor
  · intro h hnq hp
    sorry
  · intro h hp
    sorry
\`\`\`

<details>
<summary>정답 보기</summary>

\`\`\`lean
theorem contrapos_exercise (p q : Prop) : (p → q) ↔ (¬q → ¬p) := by
  constructor
  · intro h hnq hp
    exact hnq (h hp)
  · intro h hp
    by_contra hnq
    exact h hnq hp
\`\`\`

</details>

---

## 4-2.12 연습 문제: 분배 법칙

### 연습 12: ∨가 ∧에 분배

**문제:** \`p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r)\`를 증명하라.

\`\`\`lean
-- 스켈레톤
theorem dist_or_and_exercise (p q r : Prop) : 
    (p ∨ (q ∧ r)) ↔ ((p ∨ q) ∧ (p ∨ r)) := by
  constructor
  · intro h
    cases h with
    | inl hp =>
      sorry
    | inr hqr =>
      sorry
  · intro ⟨hpq, hpr⟩
    sorry
\`\`\`

<details>
<summary>정답 보기</summary>

\`\`\`lean
theorem dist_or_and_exercise (p q r : Prop) : 
    (p ∨ (q ∧ r)) ↔ ((p ∨ q) ∧ (p ∨ r)) := by
  constructor
  · intro h
    cases h with
    | inl hp =>
      exact ⟨Or.inl hp, Or.inl hp⟩
    | inr hqr =>
      exact ⟨Or.inr hqr.1, Or.inr hqr.2⟩
  · intro ⟨hpq, hpr⟩
    cases hpq with
    | inl hp => exact Or.inl hp
    | inr hq =>
      cases hpr with
      | inl hp => exact Or.inl hp
      | inr hr => exact Or.inr ⟨hq, hr⟩
\`\`\`

</details>

---

### 연습 13: ∧가 ∨에 분배

**문제:** \`p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r)\`를 증명하라.

\`\`\`lean
-- 스켈레톤
theorem dist_and_or_exercise (p q r : Prop) : 
    (p ∧ (q ∨ r)) ↔ ((p ∧ q) ∨ (p ∧ r)) := by
  constructor
  · intro ⟨hp, hqr⟩
    sorry
  · intro h
    sorry
\`\`\`

<details>
<summary>정답 보기</summary>

\`\`\`lean
theorem dist_and_or_exercise (p q r : Prop) : 
    (p ∧ (q ∨ r)) ↔ ((p ∧ q) ∨ (p ∧ r)) := by
  constructor
  · intro ⟨hp, hqr⟩
    cases hqr with
    | inl hq => exact Or.inl ⟨hp, hq⟩
    | inr hr => exact Or.inr ⟨hp, hr⟩
  · intro h
    cases h with
    | inl hpq => exact ⟨hpq.1, Or.inl hpq.2⟩
    | inr hpr => exact ⟨hpr.1, Or.inr hpr.2⟩
\`\`\`

</details>

---

## 4-2.13 연습 문제: 흡수 법칙과 결합 법칙

### 연습 14: 흡수 법칙

**문제:** \`p ∨ (p ∧ q) ↔ p\`를 증명하라.

\`\`\`lean
-- 스켈레톤
theorem absorption_exercise (p q : Prop) : (p ∨ (p ∧ q)) ↔ p := by
  constructor
  · intro h
    sorry
  · intro hp
    sorry
\`\`\`

<details>
<summary>정답 보기</summary>

\`\`\`lean
theorem absorption_exercise (p q : Prop) : (p ∨ (p ∧ q)) ↔ p := by
  constructor
  · intro h
    cases h with
    | inl hp => exact hp
    | inr hpq => exact hpq.1
  · intro hp
    exact Or.inl hp
\`\`\`

</details>

---

### 연습 15: 결합 법칙 (∨)

**문제:** \`(p ∨ q) ∨ r ↔ p ∨ (q ∨ r)\`를 증명하라.

\`\`\`lean
-- 스켈레톤
theorem assoc_or_exercise (p q r : Prop) : 
    ((p ∨ q) ∨ r) ↔ (p ∨ (q ∨ r)) := by
  constructor
  · intro h
    cases h with
    | inl hpq =>
      cases hpq with
      | inl hp => sorry
      | inr hq => sorry
    | inr hr => sorry
  · intro h
    sorry
\`\`\`

<details>
<summary>정답 보기</summary>

\`\`\`lean
theorem assoc_or_exercise (p q r : Prop) : 
    ((p ∨ q) ∨ r) ↔ (p ∨ (q ∨ r)) := by
  constructor
  · intro h
    cases h with
    | inl hpq =>
      cases hpq with
      | inl hp => exact Or.inl hp
      | inr hq => exact Or.inr (Or.inl hq)
    | inr hr => exact Or.inr (Or.inr hr)
  · intro h
    cases h with
    | inl hp => exact Or.inl (Or.inl hp)
    | inr hqr =>
      cases hqr with
      | inl hq => exact Or.inl (Or.inr hq)
      | inr hr => exact Or.inr hr
\`\`\`

</details>

---

### 연습 16: 결합 법칙 (∧)

**문제:** \`(p ∧ q) ∧ r ↔ p ∧ (q ∧ r)\`를 증명하라.

\`\`\`lean
-- 스켈레톤
theorem assoc_and_exercise (p q r : Prop) : 
    ((p ∧ q) ∧ r) ↔ (p ∧ (q ∧ r)) := by
  constructor
  · intro ⟨hpq, hr⟩
    sorry
  · intro ⟨hp, hqr⟩
    sorry
\`\`\`

<details>
<summary>정답 보기</summary>

\`\`\`lean
theorem assoc_and_exercise (p q r : Prop) : 
    ((p ∧ q) ∧ r) ↔ (p ∧ (q ∧ r)) := by
  constructor
  · intro ⟨⟨hp, hq⟩, hr⟩
    exact ⟨hp, hq, hr⟩
  · intro ⟨hp, hq, hr⟩
    exact ⟨⟨hp, hq⟩, hr⟩
\`\`\`

</details>

---

## 4-2.14 연습 문제: 조건문 관련

### 연습 17: 조건문의 부정

**문제:** \`¬(p → q) ↔ p ∧ ¬q\`를 증명하라.

\`\`\`lean
-- 스켈레톤
theorem not_impl_exercise (p q : Prop) : ¬(p → q) ↔ (p ∧ ¬q) := by
  constructor
  · intro h
    constructor
    · sorry  -- p 증명
    · sorry  -- ¬q 증명
  · intro ⟨hp, hnq⟩ hpq
    sorry
\`\`\`

<details>
<summary>정답 보기</summary>

\`\`\`lean
theorem not_impl_exercise (p q : Prop) : ¬(p → q) ↔ (p ∧ ¬q) := by
  constructor
  · intro h
    constructor
    · by_contra hnp
      apply h
      intro hp
      exact False.elim (hnp hp)
    · intro hq
      apply h
      intro _
      exact hq
  · intro ⟨hp, hnq⟩ hpq
    exact hnq (hpq hp)
\`\`\`

</details>

---

### 연습 18: 복합 동치

**문제:** \`(p → q) ∧ (p → r) ↔ p → (q ∧ r)\`를 증명하라.

\`\`\`lean
-- 스켈레톤
theorem impl_and_distrib (p q r : Prop) : 
    ((p → q) ∧ (p → r)) ↔ (p → (q ∧ r)) := by
  constructor
  · intro ⟨hpq, hpr⟩ hp
    sorry
  · intro h
    constructor
    · intro hp
      sorry
    · intro hp
      sorry
\`\`\`

<details>
<summary>정답 보기</summary>

\`\`\`lean
theorem impl_and_distrib (p q r : Prop) : 
    ((p → q) ∧ (p → r)) ↔ (p → (q ∧ r)) := by
  constructor
  · intro ⟨hpq, hpr⟩ hp
    exact ⟨hpq hp, hpr hp⟩
  · intro h
    constructor
    · intro hp
      exact (h hp).1
    · intro hp
      exact (h hp).2
\`\`\`

</details>

---

## 4-2.15 도전 문제

### 도전 1: 예제 6 (교재)

**문제:** \`¬(p → q)\`와 \`p ∧ ¬q\`가 논리적으로 동치임을 단계별로 증명하라.

교재 풀이:
1. \`¬(p → q) ≡ ¬(¬p ∨ q)\` (조건-논리합 동치)
2. \`≡ ¬(¬p) ∧ ¬q\` (제2 드 모르간 법칙)
3. \`≡ p ∧ ¬q\` (이중 부정)

\`\`\`lean
-- 스켈레톤: 직접 증명
theorem example6 (p q : Prop) : ¬(p → q) ↔ (p ∧ ¬q) := by
  sorry
\`\`\`

<details>
<summary>정답 보기</summary>

\`\`\`lean
theorem example6 (p q : Prop) : ¬(p → q) ↔ (p ∧ ¬q) := by
  constructor
  · intro h
    constructor
    · by_contra hnp
      apply h
      intro hp
      exact False.elim (hnp hp)
    · intro hq
      apply h
      intro _
      exact hq
  · intro ⟨hp, hnq⟩ hpq
    exact hnq (hpq hp)
\`\`\`

</details>

---

### 도전 2: 예제 7 (교재)

**문제:** \`¬(p ∨ (¬p ∧ q))\`와 \`¬p ∧ ¬q\`가 논리적으로 동치임을 증명하라.

\`\`\`lean
-- 스켈레톤
theorem example7 (p q : Prop) : ¬(p ∨ (¬p ∧ q)) ↔ (¬p ∧ ¬q) := by
  sorry
\`\`\`

<details>
<summary>정답 보기</summary>

\`\`\`lean
theorem example7 (p q : Prop) : ¬(p ∨ (¬p ∧ q)) ↔ (¬p ∧ ¬q) := by
  constructor
  · intro h
    constructor
    · intro hp
      exact h (Or.inl hp)
    · intro hq
      by_cases hp : p
      · exact h (Or.inl hp)
      · exact h (Or.inr ⟨hp, hq⟩)
  · intro ⟨hnp, hnq⟩ h
    cases h with
    | inl hp => exact hnp hp
    | inr hpq => exact hnq hpq.2
\`\`\`

</details>

---

### 도전 3: 예제 8 (교재)

**문제:** \`(p ∧ q) → (p ∨ q)\`가 항진명제임을 증명하라.

\`\`\`lean
-- 스켈레톤
theorem example8 (p q : Prop) : (p ∧ q) → (p ∨ q) := by
  sorry
\`\`\`

<details>
<summary>정답 보기</summary>

\`\`\`lean
theorem example8 (p q : Prop) : (p ∧ q) → (p ∨ q) := by
  intro ⟨hp, _⟩
  exact Or.inl hp
\`\`\`

</details>

---

## 4-2.16 전술 요약

### 이 장에서 사용한 전술들

| 전술 | 용도 | 상세 설명 |
|------|------|----------|
| \`constructor\` | ↔, ∧ 증명 시 두 방향으로 분리 | 3편 3.11절 |
| \`intro\` | 가정 도입 | 3편 3.8절 |
| \`exact\` | 목표와 일치하는 증거 제시 | 3편 3.9절 |
| \`cases h with\` | 논리합, 논리곱 분해 | 3편 3.11~3.12절 |
| \`Or.inl\`, \`Or.inr\` | 논리합 구성 | 3편 3.12절 |
| \`by_cases hp : p\` | 경우 분류 (배중률) | 4-1편 |
| \`by_contra hnp\` | 귀류법 | 4-1편 |
| \`h.mp\`, \`h.mpr\` | ↔에서 각 방향 추출 | 이 장 |
| \`trivial\` | True 증명 | 자동 |
| \`False.elim\` | False에서 무엇이든 유도 | 3편 |

### Lean4 라이브러리 활용

\`\`\`lean
-- 많은 논리적 동치가 이미 증명되어 있다
#check Or.comm        -- p ∨ q ↔ q ∨ p
#check And.comm       -- p ∧ q ↔ q ∧ p
#check not_not        -- ¬¬a ↔ a
#check imp_iff_not_or -- p → q ↔ ¬p ∨ q
#check Classical.em   -- p ∨ ¬p
\`\`\`

---

## 다음 편 예고

**제5편: 술어 논리와 한정기호**에서는:
- 전칭 한정기호 ∀
- 존재 한정기호 ∃
- 한정기호의 부정
- 중첩 한정기호

를 자세히 다룬다.
