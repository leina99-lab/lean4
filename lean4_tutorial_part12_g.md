# Part 12-G: 부분순서 — 기초편 (Partial Orders — Basics)

> **Rosen 이산수학 8판 · Section 9.6 기반**
> 『Mathematics in Lean』 + Lean 4 공식화

---

## 0. 들어가며: 이 파트에서 배울 것

Part 12-F에서 동치관계를 배웠다. 동치관계는 "같다"를 일반화한 것이었다. 이번에는 **"크기를 비교한다"를 일반화한 것**, 즉 **부분순서**(partial order)를 배운다.

우리는 일상에서 다양한 "순서"를 사용한다:
- 숫자의 크기: 3 ≤ 5
- 집합의 포함: {1} ⊆ {1, 2, 3}
- 약수 관계: 3 | 12
- 사전에서 단어의 순서: apple < banana

이들은 모두 **부분순서**의 예이다. "부분"이라는 말이 붙은 이유는, **모든 원소 쌍이 비교 가능하지는 않기 때문**이다. 예를 들어 집합 {1, 2}와 {2, 3}은 포함 관계로 비교할 수 없다!

### 이 파트의 구성

| 섹션 | 내용 |
|------|------|
| 1 | **부분순서의 정의** — 반사적 + 반대칭적 + 전이적 |
| 2 | **부분순서의 예** — ≤, ⊆, \|, 부분순서가 아닌 예 |
| 3 | **Lean 4의 `PartialOrder`** — 타입 클래스 시스템 |
| 4 | **비교가능성과 전체순서** — comparable, total order |
| 5 | **순서화 집합** — well-ordered set |
| 6 | **사전식 순서** — lexicographic order |
| 7 | **하세 도표** — Hasse diagram |
| 8 | **Lean 4 기초 연습** — 부분순서 증명 실습 |

### 핵심 Lean 4 개념 미리보기

| 개념 | 설명 |
|------|------|
| `PartialOrder` | 부분순서가 있는 타입 |
| `LinearOrder` | 전체순서(모든 원소가 비교가능) |
| `le_refl` | 반사성: a ≤ a |
| `le_antisymm` | 반대칭성: a ≤ b → b ≤ a → a = b |
| `le_trans` | 전이성: a ≤ b → b ≤ c → a ≤ c |
| `lt_iff_le_and_ne` | a < b ↔ a ≤ b ∧ a ≠ b |
| `Preorder` | 전순서(반사적 + 전이적, 반대칭 없음) |
| `le_total` | 전체순서에서: a ≤ b ∨ b ≤ a |

---

## 1. 부분순서의 정의

### 1.1 동치관계 vs 부분순서: 핵심 비교

Part 12-F에서 배운 **동치관계**(equivalence relation)는 "같은 종류"를 정의하는 관계였다. **부분순서**(partial order)는 "크기 순서"를 정의하는 관계이다. 둘의 핵심 차이를 표로 정리하자:

| 성질 | **동치관계** | **부분순서** |
|------|---------|---------|
| **반사적**(reflexive) | ✓ aRa | ✓ a ≤ a |
| **대칭적**(symmetric) | ✓ aRb → bRa | ✗ |
| **반대칭적**(antisymmetric) | ✗ | ✓ a ≤ b ∧ b ≤ a → a = b |
| **전이적**(transitive) | ✓ | ✓ a ≤ b ∧ b ≤ c → a ≤ c |

핵심을 한 마디로: 동치관계에서는 "a와 b가 서로 관계이면 둘은 같은 부류"이지만, 부분순서에서는 "a와 b가 서로 관계이면 둘은 **같다**"이다.

### 1.2 형식적 정의

> **정의 1** (Rosen 9.6): 집합 S에 대한 관계 R이 **반사적**(reflexive), **반대칭적**(antisymmetric), **전이적**(transitive)이면 **부분순서**(partial ordering, partial order)라고 부른다. 부분순서 R을 가진 집합 S를 **부분순서집합**(partially ordered set, poset)이라 부르고, (S, R)로 표시한다. S의 원소를 부분순서집합의 **요소**(element)라고 부른다.

각 조건을 풀어 쓰면:

1. **반사적**: 모든 a ∈ S에 대해 aRa (자기 자신과 관계)
2. **반대칭적**: aRb이고 bRa이면 a = b (양방향이면 같아야 한다)
3. **전이적**: aRb이고 bRc이면 aRc (관계가 이어진다)

### 1.3 "부분순서"라는 이름의 의미

왜 "**부분**"이라는 말이 붙었을까? 그것은 모든 원소 쌍이 반드시 비교 가능하지는 않기 때문이다. 예를 들어, 집합 {1, 2}와 {2, 3}은 포함 관계(⊆)로 비교할 수 없다: {1, 2} ⊆ {2, 3}도 아니고 {2, 3} ⊆ {1, 2}도 아니다. 이처럼 "일부 원소만" 비교할 수 있어서 "부분"순서라고 한다.

### 1.4 부분순서의 기호

부분순서집합에서 관습적으로 a ≼ b는 (a, b) ∈ R을 표현한다. 이 표기를 사용하는 이유는 실수집합에서의 "작거나 같다" 관계가 부분순서에서 가장 친숙한 예이기 때문이다. 기호 ≼는 기호 ≤와 유사하다. (기호 ≤는 어떤 부분순서집합에 대해서도 관계를 표현하는 데 사용하며, "작거나 같다" 관계만을 나타내는 것은 아니다.)

기호 a ≺ b는 a ≼ b이지만 a ≠ b라는 뜻이다. 또, a ≺ b이면 "a는 b보다 작다" 또는 "b는 a보다 크다"라고 한다.

---

## 2. 부분순서의 예

### 예제 1: 정수의 ≤ (가장 친숙한 예)

> "크거나 같다" 관계(≥)는 정수의 집합에 대해 부분순서임을 보여라.

**풀이**: 모든 정수 a에 대해 a ≥ a이므로 **반사적**이다. 만약 a ≥ b이고 b ≥ a이면 a = b이다. 따라서 ≥는 **반대칭적**이다. 마지막으로, ≥는 **전이적**인데 a ≥ b이고 b ≥ c이면 a ≥ c이기 때문이다. 따라서 ≥는 정수집합에 대해 부분순서이고 (ℤ, ≥)는 부분순서집합이다. ◀

이것은 **Lean 4에서 이미 정의되어 있다!** 바로 `PartialOrder` 인스턴스이다.

```lean
-- ℤ에는 이미 PartialOrder 인스턴스가 있다
#check (inferInstance : PartialOrder ℤ)

-- ℕ에도 있다
#check (inferInstance : PartialOrder ℕ)
```

### 예제 2: 양의 정수의 "나누다" 관계

> 9.1절에서 보인 것처럼 "나누다" 관계 |는 반사적, 반대칭적, 전이적이므로 양의 정수집합에 관해 부분순서이다. (ℤ⁺, |)는 부분순서집합이다. ℤ⁺는 양의 정수집합을 표현한다는 것을 상기하자.

```lean
-- "나누다" 관계가 부분순서임을 확인
-- 반사적: a | a
example (a : ℕ) (ha : 0 < a) : a ∣ a := dvd_refl a

-- 반대칭적: a | b ∧ b | a → a = b (양의 정수에서)
example (a b : ℕ) (ha : 0 < a) (hb : 0 < b) 
    (hab : a ∣ b) (hba : b ∣ a) : a = b :=
  Nat.dvd_antisymm hab hba

-- 전이적: a | b ∧ b | c → a | c
example (a b c : ℕ) (hab : a ∣ b) (hbc : b ∣ c) : a ∣ c :=
  dvd_trans hab hbc
```

### 예제 3: 멱집합의 포함관계

> 포함관계 ⊆이 집합 S의 멱집합에 대해 부분순서임을 보여라.

**풀이**: A가 S의 부분집합이면 항상 A ⊆ A이므로 ⊆는 **반사적**이다. 이는 반대칭적인데, A ⊆ B이고 B ⊆ A이면 A = B이기 때문이다. 마지막으로, ⊆는 **전이적**인데, A ⊆ B이고 B ⊆ C이면 A ⊆ C이기 때문이다. 따라서 ⊆는 P(S)에 대해 부분순서이고 (P(S), ⊆)는 부분순서집합이다. ◀

```lean
-- 집합의 포함관계가 부분순서임
-- Lean 4에서 Set α 위에 PartialOrder 인스턴스가 존재한다
variable {α : Type*}
#check (inferInstance : PartialOrder (Set α))

-- 반사적
example (A : Set α) : A ⊆ A := Set.Subset.refl A

-- 반대칭적
example (A B : Set α) (h1 : A ⊆ B) (h2 : B ⊆ A) : A = B :=
  Set.Subset.antisymm h1 h2

-- 전이적
example (A B C : Set α) (h1 : A ⊆ B) (h2 : B ⊆ C) : A ⊆ C :=
  Set.Subset.trans h1 h2
```

### 예제 4: 부분순서가 아닌 예

> R이 사람들에 대한 관계로, x와 y가 사람이고 x가 y보다 나이가 많으면 xRy인 관계라고 하자. R이 부분순서가 아님을 보여라.

**풀이**: R은 **반대칭적**인데, x가 y보다 나이가 많으면 y는 x보다 나이가 많지 않기 때문이다. 즉, xRy이면 y**R**x이다. R은 **전이적**인데, x가 y보다 나이가 많고 y가 z보다 나이가 많으면 x가 z보다 나이가 많기 때문이다. 즉, xRy이고 yRz이면 xRz이다. 그러나 R은 **반사적이 아닌데**, 어떤 사람도 자기 자신보다 나이가 많을 수 없기 때문이다. 즉, x**R**x이다. 따라서 R은 부분순서가 아니다. ◀

이것은 중요한 교훈을 준다: **세 가지 조건 중 하나라도 빠지면 부분순서가 아니다!**

```lean
-- 반사적이 아닌 관계의 예: 진부분집합 관계 ⊂
-- A ⊂ B는 A ⊆ B ∧ A ≠ B를 의미한다
-- 이것은 반사적이 아니다: A ⊂ A는 거짓 (A ≠ A가 거짓이므로)

example : ¬ ({1, 2} : Set ℕ) ⊂ {1, 2} := by
  intro h
  exact h.2 rfl
```

---

## 3. Lean 4의 부분순서 시스템

### 3.1 `PartialOrder` 타입 클래스

Lean 4의 Mathlib에서 부분순서는 **타입 클래스 계층구조**(type class hierarchy)로 체계적으로 관리된다. 이 계층을 이해하는 것이 Lean 4에서 순서 관련 증명을 하는 데 핵심이다.

```
              PartialOrder
             /            \
        Preorder        (반대칭성 추가)
          |
     LE (≤ 정의만)
```

각 단계를 하나씩 살펴보자:

#### 단계 1: `LE` — 비교 기호만 정의

```lean
-- LE는 ≤ 기호만 정의하는 가장 기본 클래스이다
-- 아무런 성질(공리)도 요구하지 않는다
class LE (α : Type*) where
  le : α → α → Prop
```

#### 단계 2: `Preorder` — 반사적 + 전이적

```lean
-- Preorder는 ≤가 반사적이고 전이적인 구조이다
-- 반대칭적일 필요는 없다!
class Preorder (α : Type*) extends LE α where
  le_refl : ∀ a : α, a ≤ a
  le_trans : ∀ a b c : α, a ≤ b → b ≤ c → a ≤ c
```

**전순서**(preorder)의 예: "키가 작거나 같다" 관계. 두 사람의 키가 같아도 (a ≤ b ∧ b ≤ a) 두 사람이 같은 것은 아니므로 반대칭적이 아니다. 하지만 반사적(자기 키는 자기 키보다 작거나 같다)이고 전이적(A ≤ B ≤ C이면 A ≤ C)이다.

#### 단계 3: `PartialOrder` — 반사적 + 반대칭적 + 전이적

```lean
-- PartialOrder는 Preorder에 반대칭성을 추가한 것이다
class PartialOrder (α : Type*) extends Preorder α where
  le_antisymm : ∀ a b : α, a ≤ b → b ≤ a → a = b
```

### 3.2 핵심 정리들

Lean 4에서 부분순서와 관련된 핵심 정리들이다:

```lean
variable {α : Type*} [PartialOrder α]
variable (a b c : α)

-- === 기본 세 공리 ===
#check (le_refl a : a ≤ a)                            -- 반사성
#check (le_antisymm : a ≤ b → b ≤ a → a = b)         -- 반대칭성  
#check (le_trans : a ≤ b → b ≤ c → a ≤ c)            -- 전이성

-- === 엄격 부분순서 (strict partial order) ===
-- a < b는 "a ≤ b이고 a ≠ b"와 동치이다
#check (lt_iff_le_and_ne : a < b ↔ a ≤ b ∧ a ≠ b)

-- 엄격 부분순서의 성질
#check (lt_irrefl a : ¬ (a < a))                      -- 비반사성
#check (lt_trans : a < b → b < c → a < c)             -- 전이성
#check (lt_of_le_of_lt : a ≤ b → b < c → a < c)      -- 혼합 전이
#check (lt_of_lt_of_le : a < b → b ≤ c → a < c)      -- 혼합 전이
```

### 3.3 `→` (if) vs `↔` (if and only if) 완전 이해하기

Lean 4에서 증명을 하다 보면 `→`와 `↔`를 자주 마주친다. 이 둘의 차이를 정확히 이해하는 것이 매우 중요하다!

#### `→` : **함의**(implication), "이면" (if ... then)

`P → Q`는 "P이면 Q이다"라는 뜻이다. **한쪽 방향만** 성립한다.

- **증명하려면**: `intro h`로 가정 P를 받아서 Q를 보인다
- **사용하려면**: `apply`나 `exact`로 적용한다

```lean
-- P → Q 의 예: "a ≤ b이면 a + 1 ≤ b + 1이다"
-- 한 방향만 말하고 있다
example (a b : ℕ) (h : a ≤ b) : a + 1 ≤ b + 1 := by
  omega  -- 또는 Nat.add_le_add_right h 1
```

#### `↔` : **동치**(biconditional), "필요충분조건" (if and only if)

`P ↔ Q`는 "P이면 Q이고, Q이면 P이다"라는 뜻이다. **양쪽 방향 모두** 성립한다. 수학에서 "P ⟺ Q"로 쓰는 것이다.

- **증명하려면**: `constructor`로 두 방향을 분리한 뒤 각각 증명한다
- **사용하려면**: `.mp`(정방향)나 `.mpr`(역방향)으로 한쪽만 꺼내 쓴다
- **재작성에도**: `rw`로 P를 Q로 (또는 Q를 P로) 치환할 수 있다

```lean
-- P ↔ Q 의 예: "a < b ↔ a ≤ b ∧ a ≠ b"
-- 양방향 모두 성립한다!
variable {α : Type*} [PartialOrder α] (a b : α)

-- 정방향: a < b → (a ≤ b ∧ a ≠ b)
example (h : a < b) : a ≤ b ∧ a ≠ b :=
  lt_iff_le_and_ne.mp h

-- 역방향: (a ≤ b ∧ a ≠ b) → a < b
example (h1 : a ≤ b) (h2 : a ≠ b) : a < b :=
  lt_iff_le_and_ne.mpr ⟨h1, h2⟩
```

#### 정리와 보조정리: `theorem` vs `lemma`

Lean 4에서 `theorem`과 `lemma`는 **기술적으로는 동일**하다! 둘 다 명제를 증명하는 것이다. 하지만 관습적으로:

- **정리**(theorem): 중요하고 핵심적인 결과
- **보조정리**(lemma): 정리를 증명하기 위한 중간 단계 결과

```lean
-- 이 둘은 Lean 4에서 완전히 동일하게 작동한다!
theorem my_theorem : 1 + 1 = 2 := by norm_num
lemma my_lemma : 1 + 1 = 2 := by norm_num

-- 실제 Mathlib에서는 대부분 theorem 대신 lemma를 사용한다
-- 이유: 수학적 중요도 구분보다는 일관성을 위해
```

### 3.4 치환과 대입: `rw` 전술 깊이 이해하기

**치환**(substitution/superposition)은 등식이나 동치(↔)를 이용해 목표나 가정의 일부를 바꾸는 것이다. Lean 4에서는 `rw` 전술이 이 역할을 한다.

```lean
-- rw는 등식을 이용해 치환한다
-- h : a = b 가 있을 때 rw [h]는 목표에서 a를 b로 바꾼다
example (a b c : ℕ) (h : a = b) (h2 : b + c = 10) : a + c = 10 := by
  rw [h]        -- 목표가 b + c = 10으로 변한다
  exact h2

-- rw는 ↔도 사용할 수 있다!
-- lt_iff_le_and_ne : a < b ↔ a ≤ b ∧ a ≠ b
-- rw [lt_iff_le_and_ne]는 목표에서 a < b를 a ≤ b ∧ a ≠ b로 바꾼다
variable {α : Type*} [PartialOrder α] (x y : α)

example (h1 : x ≤ y) (h2 : x ≠ y) : x < y := by
  rw [lt_iff_le_and_ne]   -- 목표: x ≤ y ∧ x ≠ y
  exact ⟨h1, h2⟩

-- 역방향 치환: rw [← h]는 b를 a로 바꾼다
example (a b c : ℕ) (h : a = b) (h2 : a + c = 10) : b + c = 10 := by
  rw [← h]      -- 목표가 a + c = 10으로 변한다
  exact h2
```

---

## 4. 비교가능성과 전체순서

### 4.1 비교가능성 (Comparable)

부분순서집합의 핵심 특징은 **모든 원소 쌍이 비교 가능하지는 않다**는 것이다.

> **정의 2** (Rosen): 부분순서집합 (S, ≼)의 원소 a와 b는 a ≼ b이거나 b ≼ a일 때 **비교가능하다**(comparable)라고 한다. S의 원소 a와 b는 a ≼ b도 b ≼ a도 아닐 때 **비교불가능하다**(incomparable)라고 한다.

### 예제 5: 나누기 관계에서의 비교가능성

> 부분순서집합(ℤ⁺, |)에서 정수 3과 9는 비교가능한가? 5와 7은 비교가능한가?

**풀이**: 정수 3과 9는 **비교가능**한데, 3 | 9이기 때문이다. 정수 5와 7은 **비교불가능**한데, 5 ∤ 7이고 7 ∤ 5이기 때문이다. ◀

```lean
-- 비교가능: 3 | 9
example : 3 ∣ 9 := ⟨3, by norm_num⟩

-- 비교불가능: 5 ∤ 7 ∧ 7 ∤ 5
example : ¬ (5 ∣ 7) := by omega
example : ¬ (7 ∣ 5) := by omega
```

### 4.2 전체순서 (Total Order)

부분순서에서 "부분"이라는 형용사는 비교불가능한 쌍이 있을 수 있기 때문이다. 집합의 모든 한 쌍의 원소가 비교가능하면 이 관계는 **전체순서**(total ordering)라고 불린다.

> **정의 3** (Rosen): (S, ≼)가 부분순서집합이고 S의 모든 두 원소가 비교가능하면, S를 **전체순서집합**(totally ordered set) 또는 **선형순서집합**(linearly ordered set)이라고 부르고, ≼를 **전체순서**(total order) 또는 **선형순서**(linear order)라고 부른다. 전체순서집합을 **사슬**(chain)이라고도 부른다.

쉽게 말해: **전체순서** = 부분순서 + "아무 두 원소나 골라도 비교할 수 있다"

### 예제 6: ℤ의 ≤는 전체순서

> 부분순서집합(ℤ, ≤)는 전체순서인데, a와 b가 정수이면 항상 a ≤ b이거나 b ≤ a이기 때문이다. ◀

### 예제 7: ℤ⁺의 |는 전체순서가 아님

> 부분순서집합(ℤ⁺, |)는 전체순서가 아닌데, 5와 7과 같은 비교불가능한 원소를 포함하기 때문이다. ◀

```lean
-- ℕ에는 전체순서(LinearOrder)가 있다
#check (inferInstance : LinearOrder ℕ)

-- 전체순서의 핵심 성질: 모든 원소가 비교가능
#check @le_total ℕ _  -- ∀ (a b : ℕ), a ≤ b ∨ b ≤ a

example (a b : ℕ) : a ≤ b ∨ b ≤ a := le_total a b
```

### 4.3 Lean 4에서의 순서 계층 구조

```
   LinearOrder (전체순서)
       |
   PartialOrder (부분순서)
       |
    Preorder (전순서)
       |
    LE (≤ 기호만)
```

```lean
-- LinearOrder는 PartialOrder보다 강하다
-- LinearOrder는 le_total을 추가로 요구한다
variable {α : Type*}

-- PartialOrder만 있으면: a ≤ b ∨ b ≤ a를 증명할 수 없다
-- LinearOrder가 있으면: 항상 a ≤ b ∨ b ≤ a가 성립한다

-- ℕ, ℤ, ℚ, ℝ는 모두 LinearOrder를 가진다
#check (inferInstance : LinearOrder ℕ)
#check (inferInstance : LinearOrder ℤ)
```

---

## 5. 순서화 집합 (Well-Ordered Set)

### 5.1 정의

> **정의 4** (Rosen): (S, ≼)는 만약 ≼가 전체순서이고, S의 모든 공집합이 아닌 부분집합이 **최소원소**(least element)를 가지면 **순서화 집합**(well-ordered set)이라고 한다.

핵심: **순서화 집합** = 전체순서 + "모든 비어있지 않은 부분집합에 최소원소가 있다"

### 예제 8: 순서화 집합의 예

> 양의 정수의 순서쌍의 집합 ℤ⁺ × ℤ⁺는 a₁ < b₁이거나, a₁ = b₁이고 a₂ ≤ b₂이면 (a₁, a₂) ≼ (b₁, b₂)인 사전식 순서에 대해 순서화 집합이다.

> 일반적인 ≤을 갖는 집합 ℤ는 순서화 집합이 아닌데, ℤ의 부분집합인 음의 정수의 집합에는 최소원소가 없기 때문이다. ◀

```lean
-- ℕ는 순서화 집합이다 (WellFoundedRelation)
-- 모든 비어있지 않은 부분집합에 최소원소가 있다
#check (inferInstance : WellFoundedRelation ℕ)

-- ℤ는 순서화 집합이 아니다 (음수 방향으로 무한)
-- 이것은 직접 증명이 필요하지만, 직관적으로 명확하다
```

### 5.2 순서화 귀납법의 원칙

> **정리 1** (순서화 귀납법의 원칙): S가 순서화 집합이라 하자. 그러면 다음을 만족하면 모든 x ∈ S에 대해 P(x)가 참이다.
> **귀납단계**: 모든 y ∈ S에 대해, x < y인 모든 x ∈ S에 대해 P(x)가 참이면 P(y)가 참이다.

이것은 Part 8에서 배운 **강한 귀납법**(strong induction)의 일반화이다! ℕ의 강한 귀납법은 (ℕ, ≤)가 순서화 집합이라는 사실의 특수한 경우이다.

---

## 6. 사전식 순서 (Lexicographic Order)

### 6.1 두 부분순서집합의 곱에 대한 사전식 순서

사전에는 단어들이 알파벳에서 글자들의 순서에 기반한 알파벳 순서, 혹은 **사전식 순서**(lexicographic order)로 나열되어 있다. 이는 집합의 부분순서로부터 만들어진 집합에 관한 문자열의 순서의 특별한 경우이다.

먼저, 두 부분순서집합 (A₁, ≼₁)과 (A₂, ≼₂)의 데카르트 곱에 대한 부분순서를 만드는 방법을 보자.

> A₁ × A₂에 대한 **사전식 순서**(lexicographic order) ≼는 첫째 쌍이 둘째 쌍보다 작다는 것은 첫째 쌍의 앞의 값이 (A₁에서) 둘째 쌍의 앞의 값보다 작거나, 앞의 값은 같지만 첫째 쌍의 뒤의 값이 (A₂에서) 둘째 쌍의 뒤의 값보다 작다는 뜻을 명시함으로 정의된다.

즉, (a₁, a₂) ≺ (b₁, b₂)는:
- a₁ <₁ b₁ **이거나**
- a₁ = b₁ **이고** a₂ <₂ b₂

일 때이다.

### 예제 9: ℤ × ℤ에서의 사전식 순서

> 부분순서집합 (ℤ × ℤ, ≼)에서 (3, 5) < (4, 8)인지, (3, 8) < (4, 5)인지, (4, 9) < (4, 11)인지 판정하라.

**풀이**: 3 < 4이므로 (3, 5) < (4, 8)이고, (3, 8) < (4, 5)이다. (4, 9)와 (4, 11)인데, 첫째 값은 같지만 9 < 11이기 때문에 (4, 9) < (4, 11)이다. ◀

```lean
-- Lean 4에서 Prod.Lex는 사전식 순서를 정의한다
-- (a₁, a₂) < (b₁, b₂) ↔ a₁ < b₁ ∨ (a₁ = b₁ ∧ a₂ < b₂)

-- 사전식 순서의 예
example : Prod.Lex (· < ·) (· < ·) (3, 5) (4, 8) := by
  left; omega     -- 3 < 4이므로

example : Prod.Lex (· < ·) (· < ·) (4, 9) (4, 11) := by
  right            -- 첫째 값이 같으므로
  constructor
  · rfl            -- 4 = 4
  · omega          -- 9 < 11
```

### 6.2 문자열의 사전식 순서

문자열의 사전식 순서는 사전에서 사용하는 것과 동일하다. 두 문자열을 왼쪽부터 비교하여 처음으로 다른 위치에서 알파벳 순서로 비교하거나, 한 문자열이 다른 문자열의 접두사이면 짧은 문자열이 더 작다.

### 예제 11: 영어 문자열의 사전식 순서

예를 들어:
- discreet < discrete (일곱 번째 위치에서 처음으로 다르고 e < t)
- discreet < discreetness (처음 여덟 글자는 같지만 두 번째 문자열이 더 길다)
- discrete < discretion (처음 여덟 글자는 같지만 두 번째 문자열이 더 길다)
- discrete < discreti (이것은 맞지 않다! discrete의 마지막 e와 discreti의 i를 비교하면 e < i이기 때문에 discrete < discreti이다)

---

## 7. 하세 도표 (Hasse Diagram)

### 7.1 필요성

유한한 부분순서집합의 방향성 그래프에서 많은 모서리들은 반드시 존재하는 것이기 때문에, 그려서 표시할 필요가 없다. 예를 들어, 집합 {1, 2, 3, 4}에 대한 부분순서 {(a, b) | a ≤ b}에 대한 방향성 그래프를 생각해 보자.

이 관계는 부분순서이기 때문에:
- **반사적**이므로 모든 꼭지점에 루프 (a, a)가 있다 → **루프를 지울 수 있다**
- **전이적**이므로 (1, 3), (1, 4), (2, 4)와 같은 모서리들은 반드시 있어야 한다 → **전이적으로 알 수 있는 모서리를 지울 수 있다**
- 모든 모서리의 화살표를 제거하고 "위를" 향하게 배치하면 방향을 보일 필요도 없다

### 7.2 하세 도표의 정의

이 과정들은 명확하게 정의되었고, 유한한 부분순서집합에 대해 유한한 횟수의 단계만 필요하다. 모든 단계를 마친 후 남은 도표는 부분순서를 찾는 데 충분한 정보를 가지는데, 이에 대해 설명할 것이다. 이 도표는 (S, ≼)의 **하세 도표**(Hasse diagram)라고 부르는데, 이 도표를 광범위하게 활용한 20세기 독일 수학자 헬무트 하세(Helmut Hasse)의 이름을 땄다.

### 7.3 덮음관계 (Covering Relation)

> (S, ≼)을 부분순서집합이라 하자. x < y이고 x < z < y인 z ∈ S가 없다면 원소 y ∈ S는 x를 **덮는다**(cover)고 한다. y가 x를 덮는 쌍(x, y)의 집합은 (S, ≼)의 **덮음관계**(covering relation)라고 한다.

쉽게 말해: y가 x를 덮는다 = "x와 y 사이에 끼어있는 원소가 없다"

부분순서집합의 하세도표를 설명하는 과정에서, (S, ≼)의 하세도표의 모서리는 (S, ≼)의 덮음관계의 쌍에 대응되는 위로 향하는 모서리임을 알 수 있다. 또, 우리는 덮음관계에서 부분순서를 복원할 수 있는데, 왜냐하면 이는 덮음관계의 반사적 전이적 폐쇄이기 때문이다. 이는 하세도표로부터 부분순서를 구성할 수 있다는 뜻이다.

### 예제 12: 나누기 관계의 하세도표

> {1, 2, 3, 4, 6, 8, 12}에 대한 부분순서 {(a, b) | a가 b를 나눈다}를 표현하는 하세도표를 그려라.

**풀이**: 
1. 먼저 방향성 그래프에서 시작한다
2. 모든 루프를 제거한다
3. 전이성으로 알아낼 수 있는 모든 모서리를 제거한다 (예: (1, 4), (1, 6), (1, 8), (1, 12), (2, 8), (2, 12), (3, 12))
4. 모든 모서리가 위쪽을 향하게 배치하고, 화살표를 지운다

결과:
```
       12
      / \
     4   6
    / \ / \
   2   3
    \ /
     1
```

(실제 하세도표에서 8도 포함해야 한다: 4 → 8, 8은 위쪽에 배치)

```lean
-- 하세 도표는 직접 코드로 그리지는 않지만,
-- 덮음관계를 정의할 수 있다
def covers (R : α → α → Prop) (x y : α) : Prop :=
  R x y ∧ x ≠ y ∧ ∀ z, R x z → R z y → z = x ∨ z = y

-- 나누기 관계에서의 덮음 예
-- 2는 1을 덮는다: 1 | 2이고, 1 < z < 2인 양의 정수 z가 없다
-- 4는 2를 덮는다: 2 | 4이고, 2 | z ∧ z | 4인 z는 2 또는 4뿐
-- 6은 3을 덮지 않는다? 아니, 3 | 6이고 3 < z < 6인 양의 정수 z가 6의 약수인 것은 없으므로 덮는다
```

### 예제 13: 멱집합의 하세도표

> S = {a, b, c}의 멱집합 P(S)에 대한 부분순서 {(A, B) | A ⊆ B}를 표현하는 하세도표를 그려라.

결과:
```
        {a,b,c}
       /  |  \
    {a,b} {a,c} {b,c}
      | \  / \  / |
      {a}  {b}  {c}
       \   |   /
         ∅
```

이것은 3차원 정육면체(큐브)의 꼴이다! 원소가 n개인 집합의 멱집합 하세도표는 n차원 초입방체와 같은 구조이다.

---

## 8. Lean 4 기초 연습

이제 지금까지 배운 내용을 Lean 4로 직접 증명해 보자. **설명 → 괄호 채우기(skeleton) → sorry 빈칸 채우기** 순서로 진행한다.

### 연습 8.1: 반사성 증명 (설명 + skeleton)

**문제**: 자연수의 ≤가 반사적임을 증명하라.

**설명**: `le_refl`을 사용하면 된다. `le_refl a`는 `a ≤ a`의 증명이다.

```lean
-- 설명과 함께 하는 skeleton
example (n : ℕ) : n ≤ n := by
  exact ⟨_⟩   -- 빈칸을 채워라!
```

<details>
<summary>📝 답 보기</summary>

```lean
example (n : ℕ) : n ≤ n := by
  exact le_refl n
-- 또는 더 간단하게:
example (n : ℕ) : n ≤ n := le_refl n
```

</details>

### 연습 8.2: 반대칭성 활용 (skeleton)

**문제**: a ≤ b이고 b ≤ a이면 a = b임을 증명하라.

```lean
example (a b : ℕ) (h1 : a ≤ b) (h2 : b ≤ a) : a = b := by
  exact ⟨___⟩ h1 h2   -- 어떤 정리를 사용해야 할까?
```

<details>
<summary>📝 답 보기</summary>

```lean
example (a b : ℕ) (h1 : a ≤ b) (h2 : b ≤ a) : a = b := by
  exact le_antisymm h1 h2
```

</details>

### 연습 8.3: 전이성 활용 (skeleton)

**문제**: a ≤ b이고 b ≤ c이면 a ≤ c임을 증명하라.

```lean
example (a b c : ℕ) (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c := by
  exact ⟨___⟩ h1 ⟨___⟩   -- 두 빈칸을 채워라!
```

<details>
<summary>📝 답 보기</summary>

```lean
example (a b c : ℕ) (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c := by
  exact le_trans h1 h2
```

</details>

### 연습 8.4: 엄격 부등식 → 비엄격 부등식 (skeleton)

**문제**: a < b이면 a ≤ b임을 증명하라.

**힌트**: `le_of_lt`를 사용하라.

```lean
example (a b : ℕ) (h : a < b) : a ≤ b := by
  exact ⟨___⟩ h   -- 어떤 정리?
```

<details>
<summary>📝 답 보기</summary>

```lean
example (a b : ℕ) (h : a < b) : a ≤ b := by
  exact le_of_lt h
```

</details>

### 연습 8.5: lt_iff_le_and_ne 활용 (skeleton)

**문제**: a ≤ b이고 a ≠ b이면 a < b임을 증명하라.

**힌트**: `lt_iff_le_and_ne.mpr`를 사용하라. `.mpr`는 ↔의 역방향(←)이다.

```lean
example (a b : ℕ) (h1 : a ≤ b) (h2 : a ≠ b) : a < b := by
  rw [⟨___⟩]       -- ↔ 정리를 사용해 목표를 변환하라
  exact ⟨h1, ⟨___⟩⟩  -- 쌍을 만들어라
```

<details>
<summary>📝 답 보기</summary>

```lean
example (a b : ℕ) (h1 : a ≤ b) (h2 : a ≠ b) : a < b := by
  rw [lt_iff_le_and_ne]
  exact ⟨h1, h2⟩
-- 또는:
example (a b : ℕ) (h1 : a ≤ b) (h2 : a ≠ b) : a < b :=
  lt_iff_le_and_ne.mpr ⟨h1, h2⟩
```

</details>

### 연습 8.6: 혼합 전이성 (sorry)

**문제**: a ≤ b이고 b < c이면 a < c임을 증명하라.

```lean
example (a b c : ℕ) (h1 : a ≤ b) (h2 : b < c) : a < c := by
  sorry
```

<details>
<summary>📝 답 보기</summary>

```lean
example (a b c : ℕ) (h1 : a ≤ b) (h2 : b < c) : a < c := by
  exact lt_of_le_of_lt h1 h2
```

</details>

### 연습 8.7: 비반사성 (sorry)

**문제**: a < a가 거짓임을 증명하라.

```lean
example (a : ℕ) : ¬ (a < a) := by
  sorry
```

<details>
<summary>📝 답 보기</summary>

```lean
example (a : ℕ) : ¬ (a < a) := by
  exact lt_irrefl a
```

</details>

### 연습 8.8: 전체순서의 성질 (sorry)

**문제**: 자연수에서 a ≤ b ∨ b ≤ a임을 증명하라.

```lean
example (a b : ℕ) : a ≤ b ∨ b ≤ a := by
  sorry
```

<details>
<summary>📝 답 보기</summary>

```lean
example (a b : ℕ) : a ≤ b ∨ b ≤ a := by
  exact le_total a b
```

</details>

### 연습 8.9: ↔ 증명하기 (sorry)

**문제**: 일반적인 부분순서에서 a < b ↔ a ≤ b ∧ a ≠ b임을 증명하라.

**힌트**: `constructor`로 두 방향을 분리하고 각각 증명하라.

```lean
variable {α : Type*} [PartialOrder α]

example (a b : α) : a < b ↔ a ≤ b ∧ a ≠ b := by
  sorry
```

<details>
<summary>📝 답 보기</summary>

```lean
variable {α : Type*} [PartialOrder α]

example (a b : α) : a < b ↔ a ≤ b ∧ a ≠ b := by
  exact lt_iff_le_and_ne
-- 또는 직접 증명:
example (a b : α) : a < b ↔ a ≤ b ∧ a ≠ b := by
  constructor
  · intro h
    exact ⟨le_of_lt h, ne_of_lt h⟩
  · intro ⟨h1, h2⟩
    exact lt_of_le_of_ne h1 h2
```

</details>

### 연습 8.10: calc를 이용한 연쇄 부등식 (sorry)

**문제**: a ≤ b, b ≤ c, c ≤ d이면 a ≤ d임을 증명하라. `calc`를 사용하라.

```lean
example (a b c d : ℕ) (h1 : a ≤ b) (h2 : b ≤ c) (h3 : c ≤ d) : a ≤ d := by
  sorry
```

<details>
<summary>📝 답 보기</summary>

```lean
example (a b c d : ℕ) (h1 : a ≤ b) (h2 : b ≤ c) (h3 : c ≤ d) : a ≤ d := by
  calc a ≤ b := h1
    _ ≤ c := h2
    _ ≤ d := h3
-- 또는:
example (a b c d : ℕ) (h1 : a ≤ b) (h2 : b ≤ c) (h3 : c ≤ d) : a ≤ d := by
  exact le_trans (le_trans h1 h2) h3
-- 또는:
example (a b c d : ℕ) (h1 : a ≤ b) (h2 : b ≤ c) (h3 : c ≤ d) : a ≤ d := by
  linarith
```

</details>

### 연습 8.11: Lattice 기초 — inf의 성질 (sorry)

**문제**: 격자(lattice)에서 x ⊓ y ≤ x를 증명하라. (이것은 Lean에 이미 있는 정리이다.)

```lean
variable {α : Type*} [Lattice α] (x y : α)

example : x ⊓ y ≤ x := by
  sorry
```

<details>
<summary>📝 답 보기</summary>

```lean
variable {α : Type*} [Lattice α] (x y : α)

example : x ⊓ y ≤ x := by
  exact inf_le_left
```

</details>

### 연습 8.12: Lattice 기초 — sup의 성질 (sorry)

**문제**: 격자(lattice)에서 x ≤ x ⊔ y를 증명하라.

```lean
variable {α : Type*} [Lattice α] (x y : α)

example : x ≤ x ⊔ y := by
  sorry
```

<details>
<summary>📝 답 보기</summary>

```lean
variable {α : Type*} [Lattice α] (x y : α)

example : x ≤ x ⊔ y := by
  exact le_sup_left
```

</details>

---

## 9. 핵심 요약

1. **부분순서**(partial order)는 **반사적** + **반대칭적** + **전이적**인 관계이다.
2. **부분순서집합**(poset) (S, ≼)는 부분순서 ≼를 가진 집합 S이다.
3. 부분순서의 대표적인 예: (ℤ, ≤), (ℤ⁺, |), (P(S), ⊆).
4. **비교가능**(comparable): a ≼ b 또는 b ≼ a. **비교불가능**(incomparable): 둘 다 아님.
5. **전체순서**(total order) = 부분순서 + 모든 원소 쌍이 비교가능. (ℤ, ≤)는 전체순서, (ℤ⁺, |)는 아님.
6. **순서화 집합**(well-ordered set) = 전체순서 + 모든 비어있지 않은 부분집합에 최소원소. (ℕ, ≤)는 순서화 집합.
7. **사전식 순서**(lexicographic order): 첫 좌표 먼저 비교, 같으면 다음 좌표 비교.
8. **하세 도표**(Hasse diagram): 루프와 전이적 모서리를 제거하고 "위를 향하게" 그린 도표.
9. **덮음관계**(covering relation): x ≺ y이고 그 사이에 원소가 없는 쌍들의 집합.
10. Lean 4에서 `PartialOrder`는 `le_refl`, `le_antisymm`, `le_trans`를 요구한다.
11. `→`(if)는 한방향, `↔`(iff)는 양방향. `theorem`과 `lemma`는 Lean 4에서 동일.
12. `rw`는 등식(=)뿐 아니라 동치(↔)도 이용해 치환할 수 있다.

---

## 10. 사용된 Lean 4 전술 정리

| 전술 | 용도 | 예시 |
|------|------|------|
| `le_refl` | 반사성 a ≤ a | `exact le_refl a` |
| `le_antisymm` | 반대칭성 | `exact le_antisymm h1 h2` |
| `le_trans` | 전이성 | `exact le_trans h1 h2` |
| `lt_irrefl` | 비반사성 ¬(a < a) | `exact lt_irrefl a` |
| `lt_iff_le_and_ne` | a < b ↔ a ≤ b ∧ a ≠ b | `rw [lt_iff_le_and_ne]` |
| `le_total` | 전체순서 a ≤ b ∨ b ≤ a | `exact le_total a b` |
| `le_of_lt` | a < b → a ≤ b | `exact le_of_lt h` |
| `lt_of_le_of_lt` | a ≤ b → b < c → a < c | 혼합 전이 |
| `lt_of_lt_of_le` | a < b → b ≤ c → a < c | 혼합 전이 |
| `inf_le_left` | x ⊓ y ≤ x | 격자의 하한 |
| `le_sup_left` | x ≤ x ⊔ y | 격자의 상한 |
| `calc` | 연쇄 부등식/등식 | `calc a ≤ b := h1 ; _ ≤ c := h2` |
| `linarith` | 선형 산술 자동 증명 | 부등식 조합 |
| `omega` | 자연수/정수 산술 | 간단한 부등식 |
| `constructor` | ∧, ↔ 분리 | 양방향 증명 |
| `rw` | 치환 (=, ↔ 모두) | `rw [lt_iff_le_and_ne]` |

---

> **다음 파트 예고**: Part 12-H에서는 **극대원소와 극소원소**(maximal and minimal elements), **최대원소와 최소원소**(greatest and least elements), **상한과 하한**(upper and lower bounds), **최소상한계와 최대하한계**(lub and glb), **격자**(lattice), 그리고 **위상정렬**(topological sort)을 Lean 4로 구현한다!
