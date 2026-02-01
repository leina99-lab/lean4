# Lean4 완전 정복 가이드 — 제4-4편

## 추론 규칙과 증명의 소개 완전 정복

> **교재**: Kenneth H. Rosen, "Discrete Mathematics and Its Applications" 8판  
> **범위**: 1.6절 추론 규칙, 1.7절 증명의 소개  
> **선수 학습**: 제4-1편(명제 논리), 제4-2편(논리적 동치), 제4-3편(술어 논리와 한정기호)

---

## 4-4.0 이 장의 목표

이 장에서는 다음을 학습한다:

1. **추론**(Inference)과 **논증**(Argument)이 무엇인지
2. **정당한 논증**(Valid Argument)의 의미
3. **핵심 추론 규칙**: 긍정 논법, 부정 논법, 가설적 삼단논법, 논리합 삼단논법 등
4. **정리**(Theorem)와 **보조정리**(Lemma)의 관계
5. **조건문**(→)과 **쌍조건문**(↔)의 차이
6. **직접 증명**, **대우에 의한 증명**, **모순에 의한 증명**
7. Lean4에서 이 모든 것을 어떻게 구현하는지

---

## 4-4.1 추론의 기초 개념

### 4-4.1.1 논증(Argument)이란?

**논증**(Argument)이란 **일련의 진술들**(statements)로, 마지막 진술을 제외한 모든 진술을 **전제**(premise)라 하고, 마지막 진술을 **결론**(conclusion)이라 한다.

**예시**:

| 역할 | 진술 |
|------|------|
| 전제 1 | "If you have a current password, then you can log onto the network." |
| 전제 2 | "You have a current password." |
| **결론** | "∴ You can log onto the network." |

여기서 ∴ 기호는 "그러므로"(therefore)를 의미한다.

### 4-4.1.2 정당한 논증(Valid Argument)이란?

**정당한 논증**이란, **모든 전제가 참일 때 결론이 반드시 참**이 되는 논증이다.

수학적으로 표현하면:

$$
(p_1 \wedge p_2 \wedge \cdots \wedge p_n) \rightarrow q \text{가 항진명제}
$$

**핵심 포인트**: 논증이 "정당하다"는 것은 **형식**(form)에 관한 것이지, 전제의 **실제 진리값**과는 무관하다!

---

### 4-4.1.3 논증형식(Argument Form)이란?

**논증형식**이란 명제 변수를 사용한 복합명제들의 순열이다. 전제에 나오는 어떤 명제가 됐든 간에 명제 변수로 치환되고, **그 전제가 모두 참일 때 결론이 참이면** 그 논증형식은 **정당하다**고 한다.

**형식적 표현**:

```
p → q    (전제 1: 조건문)
p        (전제 2: 가정부 참)
─────
∴ q      (결론: 결론부도 참)
```

이것이 바로 **긍정 논법**(Modus Ponens)이다!

---

## 4-4.2 핵심 추론 규칙 8가지

### 표 1: 명제 논리의 추론 규칙

| 추론 규칙 | 형식 | 항진명제(Tautology) | 이름 |
|----------|------|---------------------|------|
| 1 | p, p → q ∴ q | (p ∧ (p → q)) → q | **긍정 논법**(Modus Ponens) |
| 2 | ¬q, p → q ∴ ¬p | (¬q ∧ (p → q)) → ¬p | **부정 논법**(Modus Tollens) |
| 3 | p → q, q → r ∴ p → r | ((p → q) ∧ (q → r)) → (p → r) | **가설적 삼단논법**(Hypothetical Syllogism) |
| 4 | p ∨ q, ¬p ∴ q | ((p ∨ q) ∧ ¬p) → q | **논리합 삼단논법**(Disjunctive Syllogism) |
| 5 | p ∴ p ∨ q | p → (p ∨ q) | **가산 논법**(Addition) |
| 6 | p ∧ q ∴ p | (p ∧ q) → p | **단순화 논법**(Simplification) |
| 7 | p, q ∴ p ∧ q | (p) ∧ (q)) → (p ∧ q) | **논리곱 논법**(Conjunction) |
| 8 | p ∨ q, ¬p ∨ r ∴ q ∨ r | ((p ∨ q) ∧ (¬p ∨ r)) → (q ∨ r) | **용해법**(Resolution) |

---

## 4-4.3 Lean4로 긍정 논법(Modus Ponens) 이해하기

### 4-4.3.1 긍정 논법이란?

**긍정 논법**(Modus Ponens, 분리의 법칙, Law of Detachment)은 가장 기본적인 추론 규칙이다.

**형식**:
```
p → q    (만약 p이면 q이다)
p        (p이다)
─────
∴ q      (그러므로 q이다)
```

**일상 예시**:
- 전제 1: "If it snows today, then we will go skiing."
- 전제 2: "It is snowing today."
- 결론: "∴ We will go skiing."

### 4-4.3.2 Lean4에서 긍정 논법 기초

Lean4에서 `→`(조건문)을 다루는 방법을 먼저 이해해야 한다.

```lean
-- 긍정 논법의 가장 기본 형태
-- h1: P → Q (만약 P이면 Q)
-- h2: P     (P가 참)
-- 결론: Q   (그러므로 Q)

example (P Q : Prop) (h1 : P → Q) (h2 : P) : Q := by
  apply h1     -- h1을 적용하면, Q를 증명하려면 P를 증명해야 함
  exact h2     -- P는 h2로 이미 있음!

-- 더 간단한 방법: 함수 적용처럼!
example (P Q : Prop) (h1 : P → Q) (h2 : P) : Q := h1 h2
```

**핵심 이해**:

| Lean4 개념 | 수학적 의미 |
|------------|------------|
| `h1 : P → Q` | "P이면 Q"라는 증명 |
| `h2 : P` | "P가 참"이라는 증명 |
| `h1 h2` | h1에 h2를 "적용"하여 Q의 증명을 얻음 |

**비유**: `P → Q`는 "P를 넣으면 Q가 나오는 기계"이고, `h1 h2`는 "기계에 P를 넣는 것"이다!

---

### 4-4.3.3 연습문제: 긍정 논법 기초

#### 연습 1: 기본 긍정 논법
```lean
-- 완성하시오
example (P Q : Prop) (hpq : P → Q) (hp : P) : Q := by
  sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
example (P Q : Prop) (hpq : P → Q) (hp : P) : Q := by
  apply hpq   -- P → Q를 적용, 목표가 P로 바뀜
  exact hp    -- P는 hp로 증명됨

-- 또는 한 줄로:
example (P Q : Prop) (hpq : P → Q) (hp : P) : Q := hpq hp
```

**설명**:
- `apply hpq`: "P → Q"를 사용하겠다. Q를 증명하려면 P만 증명하면 된다.
- `exact hp`: P의 증명이 바로 hp이다.
- `hpq hp`: 함수처럼, hpq에 hp를 "적용"한다.
</details>

#### 연습 2: 연쇄 긍정 논법
```lean
-- 완성하시오: P → Q, Q → R, P가 주어졌을 때 R 증명
example (P Q R : Prop) (h1 : P → Q) (h2 : Q → R) (hp : P) : R := by
  sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
example (P Q R : Prop) (h1 : P → Q) (h2 : Q → R) (hp : P) : R := by
  apply h2       -- Q → R 적용, 목표가 Q로 바뀜
  apply h1       -- P → Q 적용, 목표가 P로 바뀜
  exact hp       -- P는 hp

-- 또는:
example (P Q R : Prop) (h1 : P → Q) (h2 : Q → R) (hp : P) : R := h2 (h1 hp)
```

**설명**:
- 먼저 h1에 hp를 적용하면 Q의 증명을 얻는다: `h1 hp : Q`
- 그 Q의 증명을 h2에 적용하면 R의 증명을 얻는다: `h2 (h1 hp) : R`
</details>

---

## 4-4.4 Lean4로 부정 논법(Modus Tollens) 이해하기

### 4-4.4.1 부정 논법이란?

**부정 논법**(Modus Tollens)은 **대우**(contrapositive)를 이용한 추론이다.

**형식**:
```
p → q    (만약 p이면 q이다)
¬q       (q가 아니다)
─────
∴ ¬p     (그러므로 p가 아니다)
```

**왜 이것이 성립할까?**

`p → q`의 **대우**는 `¬q → ¬p`이다. 조건문과 그 대우는 **논리적으로 동치**이다!

따라서:
- `p → q`가 참이면 `¬q → ¬p`도 참
- `¬q`가 참이므로, 긍정 논법에 의해 `¬p`가 참

### 4-4.4.2 Lean4에서 부정 논법

Lean4에서 부정(¬)은 `¬P = P → False`로 정의된다. 이를 이해하면 부정 논법을 쉽게 다룰 수 있다.

```lean
-- 부정 논법: (p → q) ∧ ¬q → ¬p
-- 여기서 ¬q는 q → False, ¬p는 p → False

example (P Q : Prop) (h1 : P → Q) (h2 : ¬Q) : ¬P := by
  intro hp       -- P를 가정하면 (¬P를 증명하려면 P가 주어질 때 모순을 유도)
  have hq : Q := h1 hp   -- h1에 hp를 적용하면 Q
  exact h2 hq    -- h2 : ¬Q = Q → False, hq : Q 이므로 False

-- 더 간단히:
example (P Q : Prop) (h1 : P → Q) (h2 : ¬Q) : ¬P := fun hp => h2 (h1 hp)
```

**핵심 이해**:

| 단계 | 설명 |
|------|------|
| `intro hp` | "P가 참이라고 가정하자"를 hp라고 부름 |
| `h1 hp` | P → Q에 P를 적용하면 Q를 얻음 |
| `h2 hq` | ¬Q(즉 Q → False)에 Q를 적용하면 False |
| 결론 | P를 가정하면 모순(False)이 나오므로 ¬P |

---

### 4-4.4.3 연습문제: 부정 논법

#### 연습 3: 기본 부정 논법
```lean
-- 완성하시오
example (P Q : Prop) (hpq : P → Q) (hnq : ¬Q) : ¬P := by
  sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
example (P Q : Prop) (hpq : P → Q) (hnq : ¬Q) : ¬P := by
  intro hp           -- P를 가정 (¬P를 증명하기 위해)
  have hq : Q := hpq hp   -- P → Q에 P를 적용하여 Q 획득
  exact hnq hq       -- ¬Q(= Q → False)에 Q를 적용하여 False

-- 또는 한 줄로:
example (P Q : Prop) (hpq : P → Q) (hnq : ¬Q) : ¬P := fun hp => hnq (hpq hp)
```

**설명**:
- `¬P`를 증명한다는 것은 "P가 참이면 모순"을 보이는 것
- P를 가정하면 Q를 얻고, ¬Q와 Q가 동시에 참이므로 모순
</details>

#### 연습 4: 부정 논법 응용
```lean
-- 교재 예제 기반: "If I am smart, then I will pass the exam. I did not pass the exam."
-- 완성하시오: ¬Passed 증명
example (Smart Passed : Prop) (h1 : Smart → Passed) (h2 : ¬Passed) : ¬Smart := by
  sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
example (Smart Passed : Prop) (h1 : Smart → Passed) (h2 : ¬Passed) : ¬Smart := by
  intro hs           -- Smart를 가정
  apply h2           -- ¬Passed = Passed → False, 목표가 Passed로 바뀜
  exact h1 hs        -- Smart → Passed에 Smart를 적용

-- 또는:
example (Smart Passed : Prop) (h1 : Smart → Passed) (h2 : ¬Passed) : ¬Smart :=
  fun hs => h2 (h1 hs)
```
</details>

---

## 4-4.5 Lean4로 가설적 삼단논법(Hypothetical Syllogism) 이해하기

### 4-4.5.1 가설적 삼단논법이란?

**가설적 삼단논법**(Hypothetical Syllogism)은 조건문들을 **연결**하는 추론이다.

**형식**:
```
p → q    (만약 p이면 q이다)
q → r    (만약 q이면 r이다)
─────
∴ p → r  (그러므로 만약 p이면 r이다)
```

**교재 예제 5**:
- 전제 1: "If it rains today, then we will not have a barbecue today."
- 전제 2: "If we do not have a barbecue today, then we will have a barbecue tomorrow."
- 결론: "∴ If it rains today, then we will have a barbecue tomorrow."

### 4-4.5.2 Lean4에서 가설적 삼단논법

```lean
-- 가설적 삼단논법: (P → Q) ∧ (Q → R) → (P → R)
example (P Q R : Prop) (h1 : P → Q) (h2 : Q → R) : P → R := by
  intro hp       -- P를 가정
  apply h2       -- Q → R 적용, 목표가 Q로 바뀜
  exact h1 hp    -- P → Q에 P를 적용하여 Q

-- 더 간단히:
example (P Q R : Prop) (h1 : P → Q) (h2 : Q → R) : P → R := fun hp => h2 (h1 hp)
```

---

### 4-4.5.3 연습문제: 가설적 삼단논법

#### 연습 5: 기본 가설적 삼단논법
```lean
-- 완성하시오
example (A B C : Prop) (hab : A → B) (hbc : B → C) : A → C := by
  sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
example (A B C : Prop) (hab : A → B) (hbc : B → C) : A → C := by
  intro ha         -- A를 가정
  apply hbc        -- B → C 적용
  exact hab ha     -- A → B에 A를 적용

-- 또는:
example (A B C : Prop) (hab : A → B) (hbc : B → C) : A → C :=
  fun ha => hbc (hab ha)
```
</details>

#### 연습 6: 3단 연쇄
```lean
-- 완성하시오: A → B, B → C, C → D로부터 A → D
example (A B C D : Prop) (h1 : A → B) (h2 : B → C) (h3 : C → D) : A → D := by
  sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
example (A B C D : Prop) (h1 : A → B) (h2 : B → C) (h3 : C → D) : A → D := by
  intro ha
  apply h3
  apply h2
  exact h1 ha

-- 또는:
example (A B C D : Prop) (h1 : A → B) (h2 : B → C) (h3 : C → D) : A → D :=
  fun ha => h3 (h2 (h1 ha))
```
</details>

---

## 4-4.6 Lean4로 논리합 삼단논법(Disjunctive Syllogism) 이해하기

### 4-4.6.1 논리합 삼단논법이란?

**논리합 삼단논법**(Disjunctive Syllogism)은 "둘 중 하나"에서 "하나가 아니면 다른 것"을 추론한다.

**형식**:
```
p ∨ q    (p 또는 q이다)
¬p       (p가 아니다)
─────
∴ q      (그러므로 q이다)
```

### 4-4.6.2 Lean4에서 논리합 삼단논법

Lean4에서 `∨`(논리합)를 다루려면 `cases` 또는 `rcases` 전술을 사용한다.

```lean
-- 논리합 삼단논법: (P ∨ Q) ∧ ¬P → Q
example (P Q : Prop) (h1 : P ∨ Q) (h2 : ¬P) : Q := by
  cases h1 with
  | inl hp =>      -- P가 참인 경우
    exfalso        -- 모순을 유도하여 Q를 증명 (False는 무엇이든 증명)
    exact h2 hp    -- ¬P와 P로부터 모순
  | inr hq =>      -- Q가 참인 경우
    exact hq       -- Q가 바로 참

-- Or.elim 사용:
example (P Q : Prop) (h1 : P ∨ Q) (h2 : ¬P) : Q :=
  Or.elim h1 (fun hp => absurd hp h2) id
```

**핵심 이해**:

| 전술 | 설명 |
|------|------|
| `cases h1` | P ∨ Q를 두 경우로 나눔: P가 참인 경우 / Q가 참인 경우 |
| `inl hp` | "왼쪽"(left)인 경우, 즉 P가 참 |
| `inr hq` | "오른쪽"(right)인 경우, 즉 Q가 참 |
| `exfalso` | 모순(False)으로부터 무엇이든 증명 |

---

### 4-4.6.3 연습문제: 논리합 삼단논법

#### 연습 7: 기본 논리합 삼단논법
```lean
-- 완성하시오
example (P Q : Prop) (hpq : P ∨ Q) (hnp : ¬P) : Q := by
  sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
example (P Q : Prop) (hpq : P ∨ Q) (hnp : ¬P) : Q := by
  cases hpq with
  | inl hp =>        -- P가 참인 경우
    exfalso          -- 모순 유도
    exact hnp hp     -- ¬P와 P
  | inr hq =>        -- Q가 참인 경우
    exact hq
```
</details>

#### 연습 8: 반대 방향
```lean
-- 완성하시오: P ∨ Q, ¬Q → P
example (P Q : Prop) (hpq : P ∨ Q) (hnq : ¬Q) : P := by
  sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
example (P Q : Prop) (hpq : P ∨ Q) (hnq : ¬Q) : P := by
  cases hpq with
  | inl hp => exact hp
  | inr hq =>
    exfalso
    exact hnq hq
```
</details>

---

## 4-4.7 Lean4로 가산 논법과 단순화 논법 이해하기

### 4-4.7.1 가산 논법(Addition)

**가산 논법**은 "참인 것에 무엇이든 OR로 붙일 수 있다"는 규칙이다.

**형식**:
```
p
─────
∴ p ∨ q
```

**Lean4 구현**:
```lean
-- 가산 논법: p → (p ∨ q)
example (P Q : Prop) (hp : P) : P ∨ Q := by
  left         -- 왼쪽(P)을 증명하겠다
  exact hp

-- 또는:
example (P Q : Prop) (hp : P) : P ∨ Q := Or.inl hp
```

### 4-4.7.2 단순화 논법(Simplification)

**단순화 논법**은 "AND에서 한 부분을 뽑아낼 수 있다"는 규칙이다.

**형식**:
```
p ∧ q
─────
∴ p
```

**Lean4 구현**:
```lean
-- 단순화 논법: (p ∧ q) → p
example (P Q : Prop) (h : P ∧ Q) : P := by
  exact h.1      -- 또는 h.left

-- 또는:
example (P Q : Prop) (h : P ∧ Q) : P := And.left h
```

---

### 4-4.7.3 연습문제: 가산 논법과 단순화 논법

#### 연습 9: 가산 논법
```lean
-- 완성하시오: Q → P ∨ Q
example (P Q : Prop) (hq : Q) : P ∨ Q := by
  sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
example (P Q : Prop) (hq : Q) : P ∨ Q := by
  right        -- 오른쪽(Q)을 증명
  exact hq

-- 또는:
example (P Q : Prop) (hq : Q) : P ∨ Q := Or.inr hq
```
</details>

#### 연습 10: 단순화 논법
```lean
-- 완성하시오: P ∧ Q → Q
example (P Q : Prop) (h : P ∧ Q) : Q := by
  sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
example (P Q : Prop) (h : P ∧ Q) : Q := by
  exact h.2      -- 또는 h.right

-- 또는:
example (P Q : Prop) (h : P ∧ Q) : Q := And.right h
```
</details>

#### 연습 11: 논리곱 논법(Conjunction)
```lean
-- 완성하시오: P, Q → P ∧ Q
example (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := by
  sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
example (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := by
  constructor    -- And.intro, 두 부분을 각각 증명
  · exact hp
  · exact hq

-- 또는:
example (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := ⟨hp, hq⟩

-- 또는:
example (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := And.intro hp hq
```
</details>

---

## 4-4.8 정리(Theorem)와 보조정리(Lemma)의 관계

### 4-4.8.1 정리란 무엇인가?

**정리**(Theorem)란 **참임을 보일 수 있는 진술**이다. 수학에서 정리는 **증명**(proof)으로 그 참임을 확인한다.

### 4-4.8.2 보조정리란 무엇인가?

**보조정리**(Lemma, 복수형 Lemmas 또는 Lemmata)란 **다른 결과를 증명하는 데 도움이 되는 덜 중요한 정리**이다.

**비유**:
- **정리(Theorem)** = 완성된 건물
- **보조정리(Lemma)** = 건물을 짓기 위한 벽돌 하나하나

### 4-4.8.3 따름정리(Corollary)와 가설(Conjecture)

- **따름정리**(Corollary): 이미 증명된 정리로부터 **직접적으로 귀결**되는 정리
- **가설**(Conjecture): 참이라고 **추측**되지만 아직 증명되지 않은 진술

### 4-4.8.4 Lean4에서 theorem과 lemma

Lean4에서 `theorem`과 `lemma`는 **기능적으로 완전히 동일**하다! 단지 의미를 구분하기 위한 표시일 뿐이다.

```lean
-- 둘은 완전히 동일하게 작동함
lemma my_lemma : P → P := fun hp => hp
theorem my_theorem : P → P := fun hp => hp

-- 실제 사용에서의 관례:
-- lemma: 작은 단계, 도우미 결과
-- theorem: 최종 목표, 중요한 결과
```

**핵심 포인트**: Lean에서 중요한 것은 `theorem`/`lemma` 키워드가 아니라, **증명이 올바른지**이다!

---

### 4-4.8.5 연습문제: 정리와 보조정리

#### 연습 12: 보조정리 정의하고 사용하기
```lean
-- 먼저 보조정리를 정의
lemma and_comm_lemma (P Q : Prop) : P ∧ Q → Q ∧ P := by
  sorry

-- 보조정리를 사용하여 정리 증명
theorem double_swap (P Q : Prop) : P ∧ Q → P ∧ Q := by
  intro h
  -- and_comm_lemma를 두 번 적용하면 원래대로 돌아옴
  sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
lemma and_comm_lemma (P Q : Prop) : P ∧ Q → Q ∧ P := by
  intro h
  constructor
  · exact h.2
  · exact h.1

theorem double_swap (P Q : Prop) : P ∧ Q → P ∧ Q := by
  intro h
  have h' : Q ∧ P := and_comm_lemma P Q h   -- 첫 번째 적용
  exact and_comm_lemma Q P h'               -- 두 번째 적용 (원래대로)
```
</details>

---

## 4-4.9 조건문(→)과 쌍조건문(↔)의 차이

### 4-4.9.1 조건문(→, if...then)

**조건문** `P → Q`는 "P이면 Q"를 의미한다.

**특성**:
- **한 방향**만 보장: P가 참이면 Q도 참
- Q가 참이라고 해서 P가 참인 것은 **아님**!

**예시**:
- "비가 오면 땅이 젖는다" (P → Q)
- 땅이 젖었다고 반드시 비가 온 것은 아님 (스프링클러일 수도!)

### 4-4.9.2 쌍조건문(↔, if and only if)

**쌍조건문** `P ↔ Q`는 "P이면 Q이고, Q이면 P이다"를 의미한다.

**특성**:
- **양 방향** 모두 성립: P ↔ Q는 (P → Q) ∧ (Q → P)와 동치
- P와 Q가 **동치**(equivalent)임을 의미

**예시**:
- "x = 0 ↔ x² = 0" (양방향 모두 성립)

### 4-4.9.3 Lean4에서 ↔ 다루기

```lean
-- ↔의 두 방향 접근
example (P Q : Prop) (h : P ↔ Q) : P → Q := h.mp   -- 또는 h.1, Iff.mp h
example (P Q : Prop) (h : P ↔ Q) : Q → P := h.mpr  -- 또는 h.2, Iff.mpr h

-- ↔ 증명하기
example (P Q : Prop) (h1 : P → Q) (h2 : Q → P) : P ↔ Q := by
  constructor
  · exact h1   -- → 방향
  · exact h2   -- ← 방향

-- 또는:
example (P Q : Prop) (h1 : P → Q) (h2 : Q → P) : P ↔ Q := ⟨h1, h2⟩
example (P Q : Prop) (h1 : P → Q) (h2 : Q → P) : P ↔ Q := Iff.intro h1 h2
```

**핵심 기억**:

| 접근 방법 | 의미 |
|----------|------|
| `h.mp` | P ↔ Q에서 P → Q 추출 (mp = modus ponens 방향) |
| `h.mpr` | P ↔ Q에서 Q → P 추출 (mpr = modus ponens reverse) |
| `h.1` | h.mp와 동일 |
| `h.2` | h.mpr와 동일 |

---

### 4-4.9.4 연습문제: 조건문과 쌍조건문

#### 연습 13: 쌍조건문의 mp 사용
```lean
-- 완성하시오
example (P Q : Prop) (h : P ↔ Q) (hp : P) : Q := by
  sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
example (P Q : Prop) (h : P ↔ Q) (hp : P) : Q := by
  exact h.mp hp

-- 또는:
example (P Q : Prop) (h : P ↔ Q) (hp : P) : Q := h.1 hp
```
</details>

#### 연습 14: 쌍조건문의 mpr 사용
```lean
-- 완성하시오
example (P Q : Prop) (h : P ↔ Q) (hq : Q) : P := by
  sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
example (P Q : Prop) (h : P ↔ Q) (hq : Q) : P := by
  exact h.mpr hq

-- 또는:
example (P Q : Prop) (h : P ↔ Q) (hq : Q) : P := h.2 hq
```
</details>

#### 연습 15: 쌍조건문 증명하기
```lean
-- 완성하시오: P ↔ P 증명 (반사성)
example (P : Prop) : P ↔ P := by
  sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
example (P : Prop) : P ↔ P := by
  constructor
  · intro hp; exact hp
  · intro hp; exact hp

-- 또는:
example (P : Prop) : P ↔ P := Iff.refl P

-- 또는:
example (P : Prop) : P ↔ P := ⟨id, id⟩
```
</details>

#### 연습 16: 쌍조건문의 대칭성
```lean
-- 완성하시오: P ↔ Q → Q ↔ P
example (P Q : Prop) (h : P ↔ Q) : Q ↔ P := by
  sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
example (P Q : Prop) (h : P ↔ Q) : Q ↔ P := by
  constructor
  · exact h.mpr
  · exact h.mp

-- 또는:
example (P Q : Prop) (h : P ↔ Q) : Q ↔ P := h.symm

-- 또는:
example (P Q : Prop) (h : P ↔ Q) : Q ↔ P := ⟨h.2, h.1⟩
```
</details>

---

## 4-4.10 증명 방법: 직접 증명

### 4-4.10.1 직접 증명(Direct Proof)이란?

**직접 증명**은 조건문 `P → Q`를 증명하는 가장 자연스러운 방법이다.

**방법**:
1. P가 참이라고 **가정**한다.
2. 정의, 공리, 이미 증명된 정리, 추론 규칙을 사용한다.
3. Q가 참임을 **보인다**.

**교재 예제 1**: "만약 n이 홀수인 정수라면 n²은 홀수인 정수이다"를 직접 증명

**증명**:
1. n이 홀수라고 가정하자.
2. 홀수의 정의에 의하여 n = 2k + 1인 정수 k가 존재한다.
3. n² = (2k + 1)² = 4k² + 4k + 1 = 2(2k² + 2k) + 1
4. 2k² + 2k는 정수이므로, n²은 홀수이다. ∎

### 4-4.10.2 Lean4에서 직접 증명

```lean
-- 간단한 직접 증명 예시
example (n : ℤ) (h : ∃ k, n = 2*k + 1) : ∃ m, n^2 = 2*m + 1 := by
  obtain ⟨k, hk⟩ := h   -- n = 2k + 1인 k가 존재
  use 2*k^2 + 2*k       -- m = 2k² + 2k로 잡자
  rw [hk]               -- n을 2k + 1로 치환
  ring                  -- 나머지는 계산
```

---

### 4-4.10.3 연습문제: 직접 증명

#### 연습 17: 짝수의 제곱
```lean
-- "n이 짝수이면 n²도 짝수이다"를 증명하시오
example (n : ℤ) (h : ∃ k, n = 2*k) : ∃ m, n^2 = 2*m := by
  sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
example (n : ℤ) (h : ∃ k, n = 2*k) : ∃ m, n^2 = 2*m := by
  obtain ⟨k, hk⟩ := h    -- n = 2k인 k가 존재
  use 2*k^2              -- m = 2k²로 잡자
  rw [hk]                -- n을 2k로 치환
  ring                   -- (2k)² = 4k² = 2·(2k²)
```

**설명**:
- `obtain ⟨k, hk⟩ := h`: 존재 한정기호를 "풀어서" 구체적인 k와 그 성질 hk를 얻음
- `use 2*k^2`: 존재 한정기호를 증명할 때, 구체적인 값을 제시
- `ring`: 다항식 계산을 자동으로 처리
</details>

#### 연습 18: 두 짝수의 합
```lean
-- "a와 b가 모두 짝수이면 a + b도 짝수이다"를 증명하시오
example (a b : ℤ) (ha : ∃ k, a = 2*k) (hb : ∃ l, b = 2*l) : ∃ m, a + b = 2*m := by
  sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
example (a b : ℤ) (ha : ∃ k, a = 2*k) (hb : ∃ l, b = 2*l) : ∃ m, a + b = 2*m := by
  obtain ⟨k, hk⟩ := ha   -- a = 2k
  obtain ⟨l, hl⟩ := hb   -- b = 2l
  use k + l              -- m = k + l
  rw [hk, hl]            -- a + b = 2k + 2l
  ring                   -- 2k + 2l = 2(k + l)
```
</details>

---

## 4-4.11 증명 방법: 대우에 의한 증명

### 4-4.11.1 대우에 의한 증명(Proof by Contraposition)이란?

**대우에 의한 증명**은 `P → Q`를 직접 증명하기 어려울 때, 그 **대우** `¬Q → ¬P`를 증명하는 방법이다.

**왜 성립하는가?**

`P → Q`와 `¬Q → ¬P`는 **논리적으로 동치**이기 때문이다!

**교재 예제 3**: "만약 3n + 2가 홀수이면 n은 홀수이다"를 대우로 증명

**대우**: "만약 n이 홀수가 아니면(= n이 짝수이면) 3n + 2가 홀수가 아니다(= 3n + 2가 짝수이다)"

**증명**:
1. n이 짝수라고 가정하자. 즉, n = 2k인 정수 k가 존재한다.
2. 3n + 2 = 3(2k) + 2 = 6k + 2 = 2(3k + 1)
3. 3k + 1은 정수이므로, 3n + 2는 짝수이다.
4. 따라서 대우가 참이므로, 원래 명제도 참이다. ∎

### 4-4.11.2 Lean4에서 대우에 의한 증명

```lean
-- 대우를 직접 사용
example (P Q : Prop) (h : ¬Q → ¬P) : P → Q := by
  intro hp             -- P를 가정
  by_contra hnq        -- Q가 아니라고 가정하여 모순 유도
  exact h hnq hp       -- ¬Q → ¬P와 ¬Q로부터 ¬P, 그런데 P가 있으므로 모순

-- contrapose 전술 사용
example (P Q : Prop) : (¬Q → ¬P) → (P → Q) := by
  intro h
  contrapose           -- 목표가 ¬Q → ¬P로 바뀜
  exact h
```

---

### 4-4.11.3 연습문제: 대우에 의한 증명

#### 연습 19: 기본 대우
```lean
-- 완성하시오: ¬Q → ¬P를 이용하여 P → Q 증명
example (P Q : Prop) (h : ¬Q → ¬P) : P → Q := by
  sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
example (P Q : Prop) (h : ¬Q → ¬P) : P → Q := by
  intro hp           -- P를 가정
  by_contra hnq      -- ¬Q를 가정하여 모순 유도
  have hnp := h hnq  -- ¬Q → ¬P에 ¬Q를 적용하여 ¬P
  exact hnp hp       -- ¬P와 P로 모순

-- 또는 contrapose 사용:
example (P Q : Prop) (h : ¬Q → ¬P) : P → Q := by
  contrapose
  exact h
```
</details>

#### 연습 20: 제곱 관련 대우
```lean
-- "n²이 짝수이면 n도 짝수이다"를 대우로 증명
-- 대우: "n이 홀수이면 n²도 홀수이다"
-- (힌트: 홀수 n = 2k + 1이면 n² = 4k² + 4k + 1 = 2(2k² + 2k) + 1)
example (n : ℤ) (h : ∃ k, n^2 = 2*k) : ∃ m, n = 2*m := by
  -- 이 문제는 실제로는 더 복잡한 수론이 필요함
  -- 여기서는 대우의 개념 이해에 집중
  sorry
```

<details>
<summary>💡 힌트</summary>

이 문제는 실제로 정수론의 깊은 결과가 필요하다. 교재에서는 개념 설명용으로 사용하지만, Lean4에서 엄밀하게 증명하려면 추가적인 보조정리가 필요하다.

개념적으로:
- 대우: "n이 홀수이면 n²도 홀수"
- n = 2k + 1이면 n² = (2k+1)² = 4k² + 4k + 1 = 2(2k² + 2k) + 1로 홀수

Lean4에서 완전히 증명하려면 `Int.even_or_odd`와 같은 보조정리를 사용해야 한다.
</details>

---

## 4-4.12 증명 방법: 모순에 의한 증명

### 4-4.12.1 모순에 의한 증명(Proof by Contradiction)이란?

**모순에 의한 증명**은 P를 증명하기 위해:
1. ¬P를 가정한다.
2. 모순을 유도한다.
3. 따라서 P가 참이어야 한다.

**형식적으로**: `¬P → False`를 보이면 P가 증명된다.

**교재 예제 10**: "임의의 22일 중에 적어도 4일은 같은 요일이 되는 것이 있음을 보여라"

**증명**(모순):
1. 22일 중에 많아야 3일이 같은 요일이라고 가정하자.
2. 한 주에는 7일이 있으므로, 각 요일에 대하여 많아야 3일이 같은 요일이면 최대 21일이 되어야 한다.
3. 이것은 22일이라는 가정에 모순이다.
4. 따라서 적어도 4일은 같은 요일이 된다. ∎

### 4-4.12.2 Lean4에서 모순에 의한 증명

```lean
-- 모순에 의한 증명의 기본 패턴
example (P : Prop) (h : ¬P → False) : P := by
  by_contra hp     -- ¬P를 가정
  exact h hp       -- ¬P → False에 ¬P를 적용하여 모순

-- 또는 Classical.byContradiction 사용
example (P : Prop) (h : ¬P → False) : P := Classical.byContradiction h
```

**핵심 전술**:

| 전술 | 의미 |
|------|------|
| `by_contra hp` | "P가 아니라고 가정하고 모순을 유도하자" |
| `exfalso` | "False를 증명하여 무엇이든 결론짓자" |
| `absurd` | 모순되는 두 진술에서 False 유도 |

---

### 4-4.12.3 연습문제: 모순에 의한 증명

#### 연습 21: 기본 모순 증명
```lean
-- 완성하시오: ¬P가 모순을 일으키면 P
example (P : Prop) (h : ¬P → False) : P := by
  sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
example (P : Prop) (h : ¬P → False) : P := by
  by_contra hp     -- ¬P를 가정
  exact h hp       -- h에 ¬P를 적용하면 False
```
</details>

#### 연습 22: 이중 부정 제거
```lean
-- 완성하시오: ¬¬P → P (배중률 기반)
example (P : Prop) (h : ¬¬P) : P := by
  sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
example (P : Prop) (h : ¬¬P) : P := by
  by_contra hp     -- ¬P를 가정
  exact h hp       -- h : ¬¬P = ¬P → False에 hp : ¬P를 적용

-- 또는:
example (P : Prop) (h : ¬¬P) : P := Classical.not_not.mp h
```
</details>

#### 연습 23: √2가 무리수임 (개념적)
```lean
-- 이것은 유명한 모순에 의한 증명의 예시이다
-- 실제 Lean 증명은 매우 복잡하므로, 개념만 이해하자

-- √2가 유리수라고 가정하면
-- √2 = a/b (a, b는 서로소인 정수, b ≠ 0)
-- 2 = a²/b²
-- 2b² = a²
-- a²이 짝수이므로 a도 짝수 (대우에 의한 증명으로 알 수 있음)
-- a = 2c라 하면 2b² = 4c², 즉 b² = 2c²
-- b²이 짝수이므로 b도 짝수
-- 그런데 a와 b가 모두 짝수이면 서로소가 아니므로 모순!
-- 따라서 √2는 무리수이다.

-- (Lean에서 완전한 증명은 Mathlib의 Real.sqrt_two_irrational 참조)
```

---

## 4-4.13 한정기호를 사용한 명제의 추론 규칙

### 4-4.13.1 전칭 예시화(Universal Instantiation)

**전칭 예시화**: ∀x P(x)가 참이면, 정의역의 임의의 원소 c에 대해 P(c)가 참이다.

**형식**:
```
∀x P(x)
─────
∴ P(c)   (c는 정의역의 임의의 원소)
```

**Lean4 구현**:
```lean
-- 전칭 예시화: ∀x, P x가 있으면 특정 값에 적용 가능
example (P : α → Prop) (h : ∀ x, P x) (c : α) : P c := by
  exact h c   -- h를 c에 적용
```

### 4-4.13.2 전칭 일반화(Universal Generalization)

**전칭 일반화**: 임의의 원소 c에 대해 P(c)가 참이면, ∀x P(x)가 참이다.

**형식**:
```
P(c)     (임의의 c에 대하여)
─────
∴ ∀x P(x)
```

**Lean4 구현**:
```lean
-- 전칭 일반화: intro로 임의의 x를 도입
example (P : α → Prop) (h : ∀ c : α, P c) : ∀ x, P x := by
  intro x      -- 임의의 x를 도입
  exact h x    -- h를 x에 적용
```

### 4-4.13.3 존재 예시화(Existential Instantiation)

**존재 예시화**: ∃x P(x)가 참이면, P(c)가 참인 어떤 원소 c가 존재한다.

**Lean4 구현**:
```lean
-- 존재 예시화: obtain 또는 rcases로 존재 한정기호를 풀기
example (P : α → Prop) (h : ∃ x, P x) : ∃ y, P y := by
  obtain ⟨c, hc⟩ := h   -- P(c)가 참인 c가 존재
  exact ⟨c, hc⟩         -- 그 c를 그대로 사용
```

### 4-4.13.4 존재 일반화(Existential Generalization)

**존재 일반화**: 특정 원소 c에 대해 P(c)가 참이면, ∃x P(x)가 참이다.

**Lean4 구현**:
```lean
-- 존재 일반화: use로 구체적인 값 제시
example (P : α → Prop) (c : α) (hc : P c) : ∃ x, P x := by
  use c        -- c가 그 x이다
  exact hc     -- P c가 참
```

---

### 4-4.13.5 연습문제: 한정기호 추론

#### 연습 24: 전칭 예시화
```lean
-- 완성하시오
example (P : ℕ → Prop) (h : ∀ n, P n) : P 42 := by
  sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
example (P : ℕ → Prop) (h : ∀ n, P n) : P 42 := by
  exact h 42

-- 또는:
example (P : ℕ → Prop) (h : ∀ n, P n) : P 42 := h 42
```
</details>

#### 연습 25: 전칭 일반화
```lean
-- 완성하시오
example (P : ℕ → Prop) (h : ∀ n, P n) : ∀ m, P m := by
  sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
example (P : ℕ → Prop) (h : ∀ n, P n) : ∀ m, P m := by
  intro m
  exact h m

-- 또는 그냥:
example (P : ℕ → Prop) (h : ∀ n, P n) : ∀ m, P m := h
```
</details>

#### 연습 26: 존재 일반화
```lean
-- 완성하시오: 5는 홀수이므로, 홀수가 존재한다
example : ∃ n : ℕ, n % 2 = 1 := by
  sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
example : ∃ n : ℕ, n % 2 = 1 := by
  use 5        -- n = 5를 제시
  norm_num     -- 5 % 2 = 1 확인

-- 또는:
example : ∃ n : ℕ, n % 2 = 1 := ⟨5, rfl⟩
```
</details>

#### 연습 27: 존재 예시화
```lean
-- 완성하시오: 짝수가 존재하면, 그 짝수에 2를 더해도 짝수
example (h : ∃ n : ℕ, n % 2 = 0) : ∃ m : ℕ, (m + 2) % 2 = 0 := by
  sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
example (h : ∃ n : ℕ, n % 2 = 0) : ∃ m : ℕ, (m + 2) % 2 = 0 := by
  obtain ⟨n, hn⟩ := h    -- n % 2 = 0인 n이 존재
  use n                  -- m = n으로 잡자
  omega                  -- n이 짝수이면 n + 2도 짝수
```
</details>

---

## 4-4.14 전칭 긍정 논법과 전칭 부정 논법

### 4-4.14.1 전칭 긍정 논법(Universal Modus Ponens)

**전칭 긍정 논법**: 전칭 예시화와 긍정 논법의 결합이다.

**형식**:
```
∀x (P(x) → Q(x))
P(a)
─────
∴ Q(a)
```

**교재 예제 14**: "모든 양의 정수 n에 대하여 n이 4보다 크면 n²은 2ⁿ보다 작다"가 참이라고 가정하자. 전칭 긍정 논법을 사용하여 100² < 2¹⁰⁰임을 증명하라.

**증명**:
1. P(n)이 "n > 4"를, Q(n)이 "n² < 2ⁿ"을 나타낸다고 하자.
2. ∀n(P(n) → Q(n))이 참이라고 가정한다.
3. P(100)이 참임을 유의하라. 왜냐하면 100 > 4이기 때문이다.
4. 전칭 긍정 논법에 의하여 Q(100), 즉 100² < 2¹⁰⁰이 참이다. ∎

### 4-4.14.2 Lean4에서 전칭 긍정 논법

```lean
-- 전칭 긍정 논법
example (P Q : α → Prop) (h1 : ∀ x, P x → Q x) (h2 : P a) : Q a := by
  have h := h1 a   -- ∀x를 a로 예시화: P a → Q a
  exact h h2       -- 긍정 논법: P a와 P a → Q a로부터 Q a

-- 더 간단히:
example (P Q : α → Prop) (h1 : ∀ x, P x → Q x) (h2 : P a) : Q a := h1 a h2
```

---

### 4-4.14.3 연습문제: 전칭 긍정 논법

#### 연습 28: 전칭 긍정 논법 기본
```lean
-- 완성하시오
example (P Q : ℕ → Prop) (h1 : ∀ n, P n → Q n) (h2 : P 7) : Q 7 := by
  sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
example (P Q : ℕ → Prop) (h1 : ∀ n, P n → Q n) (h2 : P 7) : Q 7 := by
  exact h1 7 h2

-- 또는:
example (P Q : ℕ → Prop) (h1 : ∀ n, P n → Q n) (h2 : P 7) : Q 7 := h1 7 h2
```
</details>

#### 연습 29: 전칭 부정 논법
```lean
-- 전칭 부정 논법: ∀x(P(x) → Q(x)), ¬Q(a) ⊢ ¬P(a)
-- 완성하시오
example (P Q : α → Prop) (h1 : ∀ x, P x → Q x) (h2 : ¬Q a) : ¬P a := by
  sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
example (P Q : α → Prop) (h1 : ∀ x, P x → Q x) (h2 : ¬Q a) : ¬P a := by
  intro hpa        -- P a를 가정
  have hqa := h1 a hpa   -- P a → Q a와 P a로부터 Q a
  exact h2 hqa     -- ¬Q a와 Q a로 모순

-- 또는:
example (P Q : α → Prop) (h1 : ∀ x, P x → Q x) (h2 : ¬Q a) : ¬P a :=
  fun hpa => h2 (h1 a hpa)
```
</details>

---

## 4-4.15 교재 연습문제 Lean4 변환

### 교재 연습문제 1: 논증형식 구하기

> "If Socrates is human, then Socrates is mortal. Socrates is human. ∴ Socrates is mortal."

```lean
-- 이것은 긍정 논법(Modus Ponens)이다
example (Human Mortal : Prop) (h1 : Human → Mortal) (h2 : Human) : Mortal := by
  sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
example (Human Mortal : Prop) (h1 : Human → Mortal) (h2 : Human) : Mortal := by
  exact h1 h2
```
</details>

### 교재 연습문제 2: 논증형식 구하기

> "If George does not have eight legs, then he is not a spider. George is a spider. ∴ George has eight legs."

```lean
-- 분석: ¬EightLegs → ¬Spider, Spider ⊢ EightLegs
-- 이것은 부정 논법의 변형이다
example (EightLegs Spider : Prop) (h1 : ¬EightLegs → ¬Spider) (h2 : Spider) : EightLegs := by
  sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
example (EightLegs Spider : Prop) (h1 : ¬EightLegs → ¬Spider) (h2 : Spider) : EightLegs := by
  by_contra hne      -- EightLegs가 아니라고 가정
  have hns := h1 hne -- ¬EightLegs → ¬Spider에서 ¬Spider
  exact hns h2       -- ¬Spider와 Spider로 모순
```
</details>

### 교재 연습문제 3(a): 추론 규칙 식별

> "Alice is a mathematics major. Therefore, Alice is either a mathematics major or a computer science major."

```lean
-- 이것은 가산 논법(Addition)이다: P ⊢ P ∨ Q
example (MathMajor CSMajor : Prop) (h : MathMajor) : MathMajor ∨ CSMajor := by
  sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
example (MathMajor CSMajor : Prop) (h : MathMajor) : MathMajor ∨ CSMajor := by
  left
  exact h

-- 또는:
example (MathMajor CSMajor : Prop) (h : MathMajor) : MathMajor ∨ CSMajor := Or.inl h
```
</details>

### 교재 연습문제 3(b): 추론 규칙 식별

> "Jerry is a mathematics major and a computer science major. Therefore, Jerry is a mathematics major."

```lean
-- 이것은 단순화 논법(Simplification)이다: P ∧ Q ⊢ P
example (MathMajor CSMajor : Prop) (h : MathMajor ∧ CSMajor) : MathMajor := by
  sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
example (MathMajor CSMajor : Prop) (h : MathMajor ∧ CSMajor) : MathMajor := by
  exact h.1

-- 또는:
example (MathMajor CSMajor : Prop) (h : MathMajor ∧ CSMajor) : MathMajor := And.left h
```
</details>

### 교재 연습문제 3(c): 추론 규칙 식별

> "If it is rainy, then the pool will be closed. It is rainy. Therefore, the pool is closed."

```lean
-- 이것은 긍정 논법(Modus Ponens)이다
example (Rainy PoolClosed : Prop) (h1 : Rainy → PoolClosed) (h2 : Rainy) : PoolClosed := by
  sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
example (Rainy PoolClosed : Prop) (h1 : Rainy → PoolClosed) (h2 : Rainy) : PoolClosed := by
  exact h1 h2
```
</details>

### 교재 연습문제 3(e): 추론 규칙 식별

> "If I go swimming, then I will stay in the sun too long. If I stay in the sun too long, then I will sunburn. Therefore, if I go swimming, then I will sunburn."

```lean
-- 이것은 가설적 삼단논법(Hypothetical Syllogism)이다
example (Swim StayLong Sunburn : Prop) (h1 : Swim → StayLong) (h2 : StayLong → Sunburn) : Swim → Sunburn := by
  sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
example (Swim StayLong Sunburn : Prop) (h1 : Swim → StayLong) (h2 : StayLong → Sunburn) : Swim → Sunburn := by
  intro hs
  apply h2
  exact h1 hs

-- 또는:
example (Swim StayLong Sunburn : Prop) (h1 : Swim → StayLong) (h2 : StayLong → Sunburn) : Swim → Sunburn :=
  fun hs => h2 (h1 hs)
```
</details>

---

## 4-4.16 도전 문제

### 도전 1: 교재 예제 6 (복합 논증)

> "It is not sunny this afternoon and it is colder than yesterday. We will go swimming only if it is sunny. If we do not go swimming, then we will take a canoe trip. If we take a canoe trip, then we will be home by sunset."
> **결론**: "We will be home by sunset."

```lean
-- 전제들을 명제로 변환:
-- ¬Sunny ∧ Colder
-- Swimming → Sunny (대우: ¬Sunny → ¬Swimming)
-- ¬Swimming → Canoe
-- Canoe → HomeBySunset
-- 결론: HomeBySunset

example (Sunny Colder Swimming Canoe HomeBySunset : Prop)
    (h1 : ¬Sunny ∧ Colder)
    (h2 : Swimming → Sunny)
    (h3 : ¬Swimming → Canoe)
    (h4 : Canoe → HomeBySunset) : HomeBySunset := by
  sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
example (Sunny Colder Swimming Canoe HomeBySunset : Prop)
    (h1 : ¬Sunny ∧ Colder)
    (h2 : Swimming → Sunny)
    (h3 : ¬Swimming → Canoe)
    (h4 : Canoe → HomeBySunset) : HomeBySunset := by
  -- 단계 1: h1에서 ¬Sunny 추출
  have hns : ¬Sunny := h1.1
  -- 단계 2: 부정 논법 - Swimming → Sunny와 ¬Sunny로부터 ¬Swimming
  have hnsw : ¬Swimming := fun hsw => hns (h2 hsw)
  -- 단계 3: 긍정 논법 - ¬Swimming → Canoe와 ¬Swimming로부터 Canoe
  have hc : Canoe := h3 hnsw
  -- 단계 4: 긍정 논법 - Canoe → HomeBySunset와 Canoe로부터 HomeBySunset
  exact h4 hc
```
</details>

### 도전 2: 교재 예제 7 (이메일 예제)

> "If you send me an e-mail message, then I will finish writing the program."
> "If you do not send me an e-mail message, then I will go to sleep early."
> "If I go to sleep early, then I will wake up feeling refreshed."
> "If I do not finish writing the program, then I will wake up feeling refreshed."
> **결론**: ¬Q → S (프로그램을 끝내지 않으면 상쾌하게 깬다)

```lean
example (Email Finish Sleep Refreshed : Prop)
    (h1 : Email → Finish)
    (h2 : ¬Email → Sleep)
    (h3 : Sleep → Refreshed) : ¬Finish → Refreshed := by
  sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
example (Email Finish Sleep Refreshed : Prop)
    (h1 : Email → Finish)
    (h2 : ¬Email → Sleep)
    (h3 : Sleep → Refreshed) : ¬Finish → Refreshed := by
  intro hnf           -- ¬Finish를 가정
  -- 단계 1: h1의 대우: ¬Finish → ¬Email
  have hne : ¬Email := fun he => hnf (h1 he)
  -- 단계 2: ¬Email → Sleep에 ¬Email 적용
  have hs : Sleep := h2 hne
  -- 단계 3: Sleep → Refreshed에 Sleep 적용
  exact h3 hs
```
</details>

### 도전 3: 용해법(Resolution) 증명

```lean
-- 용해법: (P ∨ Q) ∧ (¬P ∨ R) → (Q ∨ R)
example (P Q R : Prop) (h1 : P ∨ Q) (h2 : ¬P ∨ R) : Q ∨ R := by
  sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
example (P Q R : Prop) (h1 : P ∨ Q) (h2 : ¬P ∨ R) : Q ∨ R := by
  cases h1 with
  | inl hp =>          -- P가 참인 경우
    cases h2 with
    | inl hnp =>       -- ¬P도 참? 모순에서 무엇이든
      exfalso
      exact hnp hp
    | inr hr =>        -- R이 참
      right
      exact hr
  | inr hq =>          -- Q가 참인 경우
    left
    exact hq
```
</details>

---

## 4-4.17 핵심 정리

### Lean4 추론 전술 요약표

| 수학적 규칙 | Lean4 전술/함수 | 사용 예시 |
|------------|----------------|----------|
| **긍정 논법** | `apply`, 함수 적용 | `h1 h2` (h1: P→Q, h2: P) |
| **부정 논법** | `intro`, `have`, 함수 적용 | P 가정 후 모순 유도 |
| **가설적 삼단논법** | `intro`, 연쇄 `apply` | `fun x => h2 (h1 x)` |
| **논리합 삼단논법** | `cases`, `exfalso` | P∨Q 분해 후 처리 |
| **가산 논법** | `left`, `right`, `Or.inl`, `Or.inr` | P에서 P∨Q |
| **단순화 논법** | `.1`, `.2`, `And.left`, `And.right` | P∧Q에서 P |
| **논리곱 논법** | `constructor`, `⟨,⟩`, `And.intro` | P, Q에서 P∧Q |
| **전칭 예시화** | 함수 적용 | `h c` (h: ∀x, P x) |
| **전칭 일반화** | `intro` | 임의의 x 도입 |
| **존재 예시화** | `obtain ⟨c, hc⟩ :=` | ∃x 풀기 |
| **존재 일반화** | `use` | ∃x 증명 |
| **대우 증명** | `contrapose`, `by_contra` | P→Q 대신 ¬Q→¬P |
| **모순 증명** | `by_contra`, `exfalso`, `absurd` | ¬P 가정하여 False |

### 조건문(→) vs 쌍조건문(↔) 비교표

| 특성 | → (if...then) | ↔ (iff) |
|------|---------------|---------|
| 방향 | 한 방향 | 양 방향 |
| 정의 | P → Q | (P → Q) ∧ (Q → P) |
| mp/mpr | N/A | `h.mp`, `h.mpr` |
| 증명법 | `intro` | `constructor` 후 두 방향 |
| 사용법 | 함수처럼 적용 | mp/mpr 선택하여 적용 |

### theorem vs lemma

| 항목 | theorem | lemma |
|------|---------|-------|
| Lean4에서의 기능 | **동일** | **동일** |
| 관례적 의미 | 중요한 최종 결과 | 도우미 보조 결과 |
| 사용 권장 | 핵심 정리 | 중간 단계 |

---

## 4-4.18 다음 장 예고

제4-5편에서는 다음을 다룰 예정이다:

1. **수학적 귀납법**(Mathematical Induction)
2. **강한 귀납법**(Strong Induction)
3. **구조적 귀납법**(Structural Induction)
4. **재귀적 정의**(Recursive Definitions)

---

## 부록: 교재 표 1 완전 Lean4 구현

```lean
-- 표 1: 명제 논리의 추론 규칙 완전 Lean4 구현

-- 1. 긍정 논법 (Modus Ponens)
theorem modus_ponens (P Q : Prop) : P ∧ (P → Q) → Q :=
  fun ⟨hp, hpq⟩ => hpq hp

-- 2. 부정 논법 (Modus Tollens)
theorem modus_tollens (P Q : Prop) : ¬Q ∧ (P → Q) → ¬P :=
  fun ⟨hnq, hpq⟩ hp => hnq (hpq hp)

-- 3. 가설적 삼단논법 (Hypothetical Syllogism)
theorem hypothetical_syllogism (P Q R : Prop) : (P → Q) ∧ (Q → R) → (P → R) :=
  fun ⟨hpq, hqr⟩ hp => hqr (hpq hp)

-- 4. 논리합 삼단논법 (Disjunctive Syllogism)
theorem disjunctive_syllogism (P Q : Prop) : (P ∨ Q) ∧ ¬P → Q :=
  fun ⟨hpq, hnp⟩ => hpq.elim (fun hp => absurd hp hnp) id

-- 5. 가산 논법 (Addition)
theorem addition (P Q : Prop) : P → (P ∨ Q) := Or.inl

-- 6. 단순화 논법 (Simplification)
theorem simplification (P Q : Prop) : (P ∧ Q) → P := And.left

-- 7. 논리곱 논법 (Conjunction)
theorem conjunction (P Q : Prop) : P → Q → (P ∧ Q) := And.intro

-- 8. 용해법 (Resolution)
theorem resolution (P Q R : Prop) : (P ∨ Q) ∧ (¬P ∨ R) → (Q ∨ R) :=
  fun ⟨hpq, hnpr⟩ =>
    hpq.elim
      (fun hp => hnpr.elim (fun hnp => absurd hp hnp) Or.inr)
      Or.inl
```

---

**수고하셨습니다!** 🎉

이 장을 완료하면 다음을 할 수 있다:
- 정당한 논증이 무엇인지 이해하고 판별할 수 있다
- 8가지 핵심 추론 규칙을 Lean4로 구현할 수 있다
- 직접 증명, 대우에 의한 증명, 모순에 의한 증명을 수행할 수 있다
- 조건문(→)과 쌍조건문(↔)의 차이를 명확히 이해한다
- 한정기호를 사용한 추론을 Lean4로 수행할 수 있다
