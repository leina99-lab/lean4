# Lean4 완전 정복 가이드 — 제4-3편

## 술어 논리와 한정기호 완전 정복

> **교재**: Kenneth H. Rosen, "Discrete Mathematics and Its Applications" 8판  
> **범위**: 1.4절 술어와 한정기호, 1.5절 중첩된 한정기호  
> **선수 학습**: 제3편(기초 전술), 제4편(치환과 계산), 제4-1편(명제 논리), 제4-2편(논리적 동치)

---

## 4-3.0 이 장의 목표

이 장에서는 다음을 학습한다:

1. **술어**(Predicate)와 **명제함수**(Propositional Function)가 무엇인지
2. **전칭 한정기호**(∀, Universal Quantifier): "모든 x에 대하여"
3. **존재 한정기호**(∃, Existential Quantifier): "어떤 x가 존재하여"
4. **한정기호의 부정**: ¬∀x P(x) ≡ ∃x ¬P(x), ¬∃x P(x) ≡ ∀x ¬P(x)
5. **중첩된 한정기호**(Nested Quantifiers): ∀x∃y, ∃x∀y 등
6. Lean4에서 한정기호를 사용한 증명 방법

---

## 4-3.1 술어(Predicate)란 무엇인가?

### 4-3.1.1 명제 논리의 한계

1.1~1.3절에서 공부한 **명제 논리**(Propositional Logic)는 강력하지만, 다음과 같은 문장을 표현할 수 없다:

> "Every computer connected to the university network is functioning properly."  
> (대학 통신망에 연결된 모든 컴퓨터는 정상 작동한다.)

이 문장의 진리값을 판정하려면, 각 컴퓨터에 대해 개별적으로 확인해야 한다. 명제 논리만으로는 이런 "모든"이나 "어떤"을 표현하기 어렵다.

이를 해결하기 위해 **술어 논리**(Predicate Logic)를 도입한다.

### 4-3.1.2 술어의 정의

**술어**(Predicate)란 **변수를 포함하는 문장**으로, 변수에 특정 값을 대입하면 명제가 되는 것이다.

**예시**:
- "x > 3"이라는 문장에서:
  - **주어**: 변수 x
  - **술어**: "is greater than 3" (3보다 크다)
  
이 문장을 P(x)로 표기하면, P는 "is greater than 3"라는 술어를 나타낸다.

| 대입 | 결과 | 진리값 |
|------|------|--------|
| P(4) | "4 > 3" | 참(True) |
| P(2) | "2 > 3" | 거짓(False) |
| P(1) | "1 > 3" | 거짓(False) |

**핵심**: P(x) 자체는 명제가 아니다! 변수 x에 값을 대입해야 비로소 명제가 된다.

### 4-3.1.3 Lean4에서의 술어

Lean4에서 술어는 **타입에서 Prop으로 가는 함수**로 표현된다.

```lean
-- 술어: 자연수를 받아서 명제를 반환하는 함수
def P (x : Nat) : Prop := x > 3

-- 술어에 값을 대입하면 명제가 된다
#check P 4      -- P 4 : Prop (명제 타입)
#check P 2      -- P 2 : Prop

-- 각 명제의 진리값을 확인할 수 있다
example : P 4 := by decide  -- 4 > 3은 참
example : ¬P 2 := by decide -- 2 > 3의 부정, 즉 2 ≤ 3은 참
```

### 4-3.1.4 n-변수 술어 (n-항 술어)

술어는 여러 변수를 가질 수 있다.

| 변수 개수 | 이름 | 예시 |
|----------|------|------|
| 1개 | 1-변수 술어 (단항 술어) | P(x): "x > 3" |
| 2개 | 2-변수 술어 (이항 술어) | Q(x, y): "x = y + 3" |
| 3개 | 3-변수 술어 (삼항 술어) | R(x, y, z): "x + y = z" |

```lean
-- 2-변수 술어
def Q (x y : Nat) : Prop := x = y + 3

example : Q 5 2 := by decide   -- 5 = 2 + 3 ✓
example : ¬Q 4 2 := by decide  -- 4 ≠ 2 + 3 ✓

-- 3-변수 술어  
def R (x y z : Nat) : Prop := x + y = z

example : R 1 2 3 := by decide   -- 1 + 2 = 3 ✓
example : ¬R 0 0 1 := by decide  -- 0 + 0 ≠ 1 ✓
```

---

## 4-3.2 전칭 한정기호(∀, Universal Quantifier)

### 4-3.2.1 전칭 한정의 정의

**전칭 한정**(Universal Quantification)은 "모든 x에 대하여 P(x)가 참이다"를 표현한다.

**기호**: ∀x P(x)  
**읽는 법**: "for all x, P(x)" 또는 "for every x, P(x)"

**정의**(Definition 1):  
> P(x)의 **전칭 한정**이란 "정의역에 속하는 x의 모든 값에 대하여 P(x)이다"라고 하는 문장이다.

| 문장 | 언제 참? | 언제 거짓? |
|------|---------|----------|
| ∀x P(x) | 모든 x에 대하여 P(x)가 참이다 | P(x)가 거짓이 되는 x가 있다 |

### 4-3.2.2 정의역(Domain)의 중요성

**핵심**: ∀x P(x)의 진리값은 **정의역**(Domain, Universe of Discourse)에 따라 달라진다!

**예제 8** (교재): P(x)가 "x + 1 > x"라는 술어라고 하자.

| 정의역 | ∀x P(x)의 진리값 |
|--------|----------------|
| 모든 실수 | **참** (모든 실수 x에 대해 x + 1 > x) |
| 모든 자연수 | **참** |

**예제 9** (교재): Q(x)가 "x < 2"라는 명제함수라 하자.

| 정의역 | ∀x Q(x)의 진리값 | 이유 |
|--------|----------------|------|
| 모든 실수 | **거짓** | 예: Q(3)은 "3 < 2"로 거짓 |

**반례**(Counterexample): ∀x P(x)가 거짓임을 보이려면, P(x)가 거짓이 되는 원소 x 하나만 찾으면 된다.

### 4-3.2.3 Lean4에서 전칭 한정기호

Lean4에서 ∀는 매우 자연스럽게 표현된다:

```lean
-- 전칭 한정: 모든 자연수 n에 대해 n + 0 = n
example : ∀ n : Nat, n + 0 = n := by
  intro n     -- "임의의 n을 고정하자"
  rfl         -- n + 0 = n은 정의에 의해 성립

-- 더 복잡한 예: 모든 자연수 n에 대해 0 + n = n
example : ∀ n : Nat, 0 + n = n := by
  intro n
  exact Nat.zero_add n  -- 라이브러리 정리 사용
```

**`intro` 전술 복습** (3편 참조):
- 목표가 `∀ x, P x` 형태일 때 사용
- "임의의 x를 고정하자"라는 의미
- x가 가정에 추가되고, 목표가 P x로 바뀜

### 4-3.2.4 유한 정의역에서의 전칭 한정

정의역이 유한하면, 전칭 한정을 **논리곱**(∧)으로 풀어쓸 수 있다.

정의역 = {x₁, x₂, ..., xₙ}일 때:  
**∀x P(x) ≡ P(x₁) ∧ P(x₂) ∧ ... ∧ P(xₙ)**

**예제 15** (교재): P(x)가 "x² < 10"이라 하고, 정의역은 "4를 초과하지 않는 양의 정수"라 하자.

정의역 = {1, 2, 3, 4}

∀x P(x) = P(1) ∧ P(2) ∧ P(3) ∧ P(4)
        = (1² < 10) ∧ (2² < 10) ∧ (3² < 10) ∧ (4² < 10)
        = (1 < 10) ∧ (4 < 10) ∧ (9 < 10) ∧ (16 < 10)
        = T ∧ T ∧ T ∧ **F**
        = **거짓**

```lean
-- 유한 정의역 예제
def isLessThan10Squared (x : Nat) : Prop := x * x < 10

-- P(4) = 16 < 10 은 거짓이므로, ∀x P(x)는 거짓
example : ¬∀ x : Fin 5, x.val > 0 → isLessThan10Squared x.val := by
  intro h
  -- x = 4일 때 반례
  have h4 := h ⟨4, by omega⟩ (by omega : 4 > 0)
  -- h4 : 4 * 4 < 10, 즉 16 < 10 → 모순
  omega
```

---

## 4-3.3 존재 한정기호(∃, Existential Quantifier)

### 4-3.3.1 존재 한정의 정의

**존재 한정**(Existential Quantification)은 "어떤 x에 대하여 P(x)가 참이다"를 표현한다.

**기호**: ∃x P(x)  
**읽는 법**: "there exists x such that P(x)" 또는 "for some x, P(x)"

**정의**(Definition 2):  
> P(x)의 **존재 한정**이란 "정의역에 속하는 적어도 하나의 값 x에 대하여 P(x)이다"라고 하는 명제이다.

| 문장 | 언제 참? | 언제 거짓? |
|------|---------|----------|
| ∃x P(x) | P(x)가 참이 되는 x가 있다 | 모든 x에 대하여 P(x)가 거짓이다 |

### 4-3.3.2 존재 한정의 예제

**예제 13** (교재): P(x)가 "x > 3"이라 하자. 정의역이 모든 실수일 때, ∃x P(x)의 진리값은?

**풀이**: x = 4일 때, "x > 3"을 만족하므로, 적어도 하나의 값이 P(x)를 만족시키므로 ∃x P(x)는 **참**이다.

**예제 14** (교재): Q(x)가 "x = x + 1"이고 정의역이 모든 실수라고 하면 ∃x Q(x)의 진리값은?

**풀이**: 모든 실수에 대하여 Q(x)를 만족시키는 x값이 하나도 존재하지 않으므로 ∃x Q(x)는 **거짓**이다.

### 4-3.3.3 Lean4에서 존재 한정기호

```lean
-- 존재 한정: 2와 3 사이의 실수가 존재한다
-- (실제로는 자연수로 간단히 예시)
example : ∃ x : Nat, x > 2 ∧ x < 5 := by
  use 3           -- "x = 3을 사용하겠다"
  constructor     -- 두 조건을 각각 증명
  · omega         -- 3 > 2
  · omega         -- 3 < 5

-- 더 간단한 예: 0보다 큰 자연수가 존재한다
example : ∃ n : Nat, n > 0 := by
  use 1           -- n = 1을 선택
  omega           -- 1 > 0 증명
```

**`use` 전술**:
- 목표가 `∃ x, P x` 형태일 때 사용
- 존재하는 값을 **직접 제시**
- "x = (제시한 값)을 사용하겠다"라는 의미

### 4-3.3.4 유한 정의역에서의 존재 한정

정의역이 유한하면, 존재 한정을 **논리합**(∨)으로 풀어쓸 수 있다.

정의역 = {x₁, x₂, ..., xₙ}일 때:  
**∃x P(x) ≡ P(x₁) ∨ P(x₂) ∨ ... ∨ P(xₙ)**

**예제 16** (교재): P(x)는 "x² > 10"을 나타내고 정의역이 "4보다 크지 않은 양의 정수"라고 할 때, ∃x P(x)의 진리값은?

정의역 = {1, 2, 3, 4}

∃x P(x) = P(1) ∨ P(2) ∨ P(3) ∨ P(4)
        = (1² > 10) ∨ (2² > 10) ∨ (3² > 10) ∨ (4² > 10)
        = F ∨ F ∨ F ∨ **T**  (16 > 10)
        = **참**

```lean
-- P(4) = 16 > 10 이므로 ∃x P(x)는 참
example : ∃ x : Fin 5, x.val > 0 ∧ x.val * x.val > 10 := by
  use ⟨4, by omega⟩  -- x = 4 선택
  constructor
  · omega            -- 4 > 0
  · omega            -- 16 > 10
```

---

## 4-3.4 한정기호의 부정 (드 모르간 법칙)

### 4-3.4.1 전칭 한정의 부정

**핵심 동치** (표 2 참조):

| 부정 | 동치 표현 | 언제 참? | 언제 거짓? |
|------|---------|---------|----------|
| ¬∀x P(x) | ∃x ¬P(x) | P(x)가 거짓인 x가 있다 | 모든 x에 대해 P(x)가 참이다 |

**직관적 이해**:
- "모든 학생이 미적분학을 수강했다"의 부정
- = "미적분학을 수강하지 않은 학생이 **존재**한다"

**증명**:
- ¬∀x P(x)가 참 ⟺ ∀x P(x)가 거짓
- ⟺ P(x)가 거짓인 원소 x가 정의역에 있다
- ⟺ ∃x ¬P(x)가 참

### 4-3.4.2 존재 한정의 부정

| 부정 | 동치 표현 | 언제 참? | 언제 거짓? |
|------|---------|---------|----------|
| ¬∃x P(x) | ∀x ¬P(x) | 모든 x에 대해 P(x)가 거짓이다 | P(x)가 참인 x가 있다 |

**직관적 이해**:
- "미적분학을 수강한 학생이 존재한다"의 부정
- = "**모든** 학생이 미적분학을 수강하지 않았다"

### 4-3.4.3 한정기호 부정에 대한 드 모르간 법칙 (표 2)

| 부정 | 동치 표현 |
|------|---------|
| ¬∃x P(x) | ∀x ¬P(x) |
| ¬∀x P(x) | ∃x ¬P(x) |

이 규칙은 명제 논리의 드 모르간 법칙과 유사하다:
- ¬(P ∨ Q) ≡ ¬P ∧ ¬Q  →  ¬∃ ≡ ∀¬
- ¬(P ∧ Q) ≡ ¬P ∨ ¬Q  →  ¬∀ ≡ ∃¬

### 4-3.4.4 Lean4에서 한정기호의 부정

```lean
-- ¬∀x P(x) ↔ ∃x ¬P(x)
example (P : α → Prop) : (¬∀ x, P x) ↔ ∃ x, ¬P x := by
  constructor
  · -- ¬∀x P(x) → ∃x ¬P(x)
    intro h
    by_contra h'        -- 귀류법: ∃x ¬P(x)가 거짓이라 가정
    push_neg at h'      -- h' : ∀x, P x
    exact h h'
  · -- ∃x ¬P(x) → ¬∀x P(x)
    intro ⟨x, hx⟩       -- 존재 한정 분해: x와 hx : ¬P x
    intro h             -- ∀x P(x)라고 가정
    exact hx (h x)      -- P x와 ¬P x가 동시에 → 모순

-- ¬∃x P(x) ↔ ∀x ¬P(x)
example (P : α → Prop) : (¬∃ x, P x) ↔ ∀ x, ¬P x := by
  constructor
  · -- ¬∃x P(x) → ∀x ¬P(x)
    intro h x hpx
    exact h ⟨x, hpx⟩    -- ∃x P(x)를 만들어서 h에 적용
  · -- ∀x ¬P(x) → ¬∃x P(x)
    intro h ⟨x, hpx⟩
    exact h x hpx        -- ¬P x와 P x가 동시에 → 모순
```

### 4-3.4.5 예제 20 (교재): 문장의 부정

"There is an honest politician"과 "All Americans eat cheeseburgers" 문장의 부정은 무엇인가?

**풀이**:
1. H(x)가 "x is honest"를 나타낸다고 하면, "There is an honest politician"이라고 하는 문장은 ∃x H(x)로 표현된다. 따라서 이 문장의 부정은:

   ¬∃x H(x) ≡ **∀x ¬H(x)**

   이것은 "Every politician is dishonest"와 동치이다.

2. C(x)가 "x eats cheeseburgers"를 나타낸다고 하자. 그러면 문장 "All Americans eat cheeseburgers"는 ∀x C(x)로 표기된다(단, 정의역은 "all Americans"이다). 이 문장의 부정은:

   ¬∀x C(x) ≡ **∃x ¬C(x)**

   이 부정은 "Some American does not eat cheeseburgers"와 같이 여러 다른 방법으로 표현될 수 있다.

---

## 4-3.5 중첩된 한정기호(Nested Quantifiers)

### 4-3.5.1 중첩 한정기호란?

한 한정기호의 범위 안에 다른 한정기호가 나타나는 것을 **중첩된 한정기호**(Nested Quantifiers)라고 한다.

**예시**: ∀x∃y(x + y = 0)
- "모든 x에 대하여, x + y = 0을 만족하는 y가 존재한다"
- 이것은 ∀x Q(x)와 같은데, 여기서 Q(x)는 ∃y P(x, y)이고, P(x, y)는 x + y = 0이다.

### 4-3.5.2 중첩 한정기호의 순서

**핵심**: 한정기호의 순서가 바뀌면 의미가 달라질 수 있다!

| 문장 | 의미 | 예(정의역: 실수) |
|------|------|-----------------|
| ∀x∀y P(x,y) | 모든 x와 모든 y에 대해 P(x,y) | ∀x∀y(x+y = y+x) - 참 |
| ∀x∃y P(x,y) | 모든 x에 대해, P(x,y)인 y가 존재 | ∀x∃y(x+y = 0) - 참 (y = -x) |
| ∃x∀y P(x,y) | 어떤 x가 있어서, 모든 y에 대해 P(x,y) | ∃x∀y(x+y = 0) - 거짓 |
| ∃x∃y P(x,y) | P(x,y)인 x와 y가 존재 | ∃x∃y(x+y = 0) - 참 (x=1, y=-1) |

### 4-3.5.3 예제 1 (교재 1.5절): 덧셈의 교환법칙

변수 x와 y의 정의역이 "모든 실수"라고 하면:

∀x∀y(x + y = y + x)

는 "모든 실수 x와 y에 대해서 x + y = y + x"라는 것을 말한다. 이것은 실수의 덧셈에 있어서 **교환 법칙**을 나타낸다.

```lean
-- 덧셈의 교환법칙
example : ∀ x y : Int, x + y = y + x := by
  intro x y
  ring  -- 대수적 등식은 ring 전술로!
```

### 4-3.5.4 예제 2-4 (교재 1.5절): 다양한 중첩 한정기호

**예제 2**: ∀x∃y(x + y = 0)
- 의미: "모든 실수 x에 대해, x + y = 0인 y가 존재한다"
- 진리값: **참** (y = -x를 선택하면 됨)

```lean
example : ∀ x : Int, ∃ y : Int, x + y = 0 := by
  intro x
  use -x      -- y = -x 선택
  ring        -- x + (-x) = 0
```

**예제 3**: ∃x∀y(x + y = 0)
- 의미: "어떤 실수 x가 있어서, 모든 y에 대해 x + y = 0"
- 진리값: **거짓** (어떤 x를 골라도 y = 1을 대입하면 x + 1 ≠ 0이 되는 x가 있음)

```lean
example : ¬∃ x : Int, ∀ y : Int, x + y = 0 := by
  intro ⟨x, h⟩
  -- h : ∀ y, x + y = 0
  have h1 := h 0      -- y = 0 대입: x + 0 = 0, 즉 x = 0
  have h2 := h 1      -- y = 1 대입: x + 1 = 0, 즉 x = -1
  omega               -- x = 0과 x = -1은 모순
```

### 4-3.5.5 같은 종류 한정기호의 순서

**중요한 성질**: 같은 종류의 한정기호는 순서를 바꿔도 의미가 같다!

| 동치 |
|------|
| ∀x∀y P(x,y) ≡ ∀y∀x P(x,y) |
| ∃x∃y P(x,y) ≡ ∃y∃x P(x,y) |

```lean
-- ∀x∀y P(x,y) ↔ ∀y∀x P(x,y)
example (P : α → β → Prop) : (∀ x y, P x y) ↔ (∀ y x, P x y) := by
  constructor
  · intro h y x
    exact h x y
  · intro h x y
    exact h y x

-- ∃x∃y P(x,y) ↔ ∃y∃x P(x,y)
example (P : α → β → Prop) : (∃ x y, P x y) ↔ (∃ y x, P x y) := by
  constructor
  · intro ⟨x, y, h⟩
    exact ⟨y, x, h⟩
  · intro ⟨y, x, h⟩
    exact ⟨x, y, h⟩
```

### 4-3.5.6 다른 종류 한정기호의 순서

**주의**: ∀x∃y P(x,y)와 ∃y∀x P(x,y)는 일반적으로 **동치가 아니다**!

| 방향 | 성립 여부 |
|------|---------|
| ∃y∀x P(x,y) → ∀x∃y P(x,y) | 항상 성립 |
| ∀x∃y P(x,y) → ∃y∀x P(x,y) | 일반적으로 **불성립** |

```lean
-- ∃y∀x P(x,y) → ∀x∃y P(x,y)는 항상 성립
example (P : α → β → Prop) : (∃ y, ∀ x, P x y) → (∀ x, ∃ y, P x y) := by
  intro ⟨y, h⟩ x
  exact ⟨y, h x⟩

-- 역방향은 일반적으로 불성립 (반례 제시)
-- "모든 사람에게는 가장 친한 친구가 있다" (∀x∃y)
-- ≠ "모든 사람의 가장 친한 친구인 사람이 존재한다" (∃y∀x)
```

---

## 4-3.6 중첩 한정기호의 부정

### 4-3.6.1 부정 방법

중첩된 한정기호의 부정은 **드 모르간 법칙을 연속적으로 적용**한다.

**예**: ¬∀x∃y P(x,y)의 부정 과정

```
¬∀x∃y P(x,y)
≡ ∃x ¬(∃y P(x,y))     -- ¬∀ ≡ ∃¬ 적용
≡ ∃x ∀y ¬P(x,y)       -- ¬∃ ≡ ∀¬ 적용
```

### 4-3.6.2 체계적인 부정 규칙

| 원래 문장 | 부정 |
|---------|------|
| ∀x∀y P(x,y) | ∃x∃y ¬P(x,y) |
| ∀x∃y P(x,y) | ∃x∀y ¬P(x,y) |
| ∃x∀y P(x,y) | ∀x∃y ¬P(x,y) |
| ∃x∃y P(x,y) | ∀x∀y ¬P(x,y) |

**규칙**: 각 한정기호를 반대로 바꾸고(∀↔∃), 맨 안쪽 술어에 부정을 붙인다.

### 4-3.6.3 Lean4에서 중첩 한정기호의 부정

```lean
-- ¬∀x∃y P(x,y) ↔ ∃x∀y ¬P(x,y)
example (P : α → β → Prop) : (¬∀ x, ∃ y, P x y) ↔ (∃ x, ∀ y, ¬P x y) := by
  push_neg  -- Lean의 push_neg 전술이 자동으로 처리!
```

**`push_neg` 전술** (4-1편에서 소개):
- 부정을 안쪽으로 밀어넣음
- 한정기호의 부정도 자동으로 처리
- ¬∀ → ∃¬, ¬∃ → ∀¬ 를 자동 적용

---

## 4-3.7 핵심 전술 정리

| 전술 | 사용 시점 | 효과 |
|------|---------|------|
| `intro x` | 목표: `∀ x, P x` | x를 가정에 추가, 목표가 P x로 |
| `use t` | 목표: `∃ x, P x` | x = t 대입, 목표가 P t로 |
| `rcases h with ⟨x, hx⟩` | 가정 h: `∃ x, P x` | x와 hx: P x 추출 |
| `specialize h t` | 가정 h: `∀ x, P x` | h를 h: P t로 특수화 |
| `push_neg` | 부정이 있을 때 | 부정을 안쪽으로 밀어넣음 |
| `by_contra` | 귀류법 증명 | 목표의 부정을 가정에 추가 |

---

## 4-3.8 연습 문제

### 연습 1: 전칭 한정 기본

P(x)가 "x ≤ 4"를 나타낸다면 다음의 진리값들은 무엇인가? (정의역: 자연수)

```lean
-- (a) P(0)
example : (0 : Nat) ≤ 4 := by
  sorry  -- 빈칸 채우기

-- (b) P(4)  
example : (4 : Nat) ≤ 4 := by
  sorry

-- (c) P(6)
example : ¬((6 : Nat) ≤ 4) := by
  sorry
```

<details>
<summary>정답 보기</summary>

```lean
-- (a) P(0): 0 ≤ 4는 참
example : (0 : Nat) ≤ 4 := by omega

-- (b) P(4): 4 ≤ 4는 참
example : (4 : Nat) ≤ 4 := by omega

-- (c) P(6): 6 ≤ 4는 거짓, 따라서 ¬P(6)가 참
example : ¬((6 : Nat) ≤ 4) := by omega
```

</details>

---

### 연습 2: 존재 한정 기본

Q(x)가 "x + 1 > 2x"라고 하는 명제함수라 하자. 정의역이 모든 정수라고 할 때 다음의 진리값을 구하라.

```lean
def Q (x : Int) : Prop := x + 1 > 2 * x

-- (a) Q(0): 0 + 1 > 0 즉 1 > 0
example : Q 0 := by
  unfold Q
  sorry

-- (b) Q(-1): -1 + 1 > -2 즉 0 > -2
example : Q (-1) := by
  unfold Q
  sorry

-- (c) Q(1): 1 + 1 > 2 즉 2 > 2
example : ¬Q 1 := by
  unfold Q
  sorry
```

<details>
<summary>정답 보기</summary>

```lean
def Q (x : Int) : Prop := x + 1 > 2 * x

-- (a) Q(0): 1 > 0은 참
example : Q 0 := by
  unfold Q
  omega

-- (b) Q(-1): 0 > -2는 참
example : Q (-1) := by
  unfold Q
  omega

-- (c) Q(1): 2 > 2는 거짓이므로 ¬Q(1)이 참
example : ¬Q 1 := by
  unfold Q
  omega
```

</details>

---

### 연습 3: 전칭 한정 증명

"모든 자연수 n에 대해 n + 0 = n"을 증명하라.

```lean
example : ∀ n : Nat, n + 0 = n := by
  sorry
```

<details>
<summary>힌트</summary>

`intro`로 임의의 n을 고정하고, `rfl`로 정의에 의한 동치를 보이면 된다.

</details>

<details>
<summary>정답 보기</summary>

```lean
example : ∀ n : Nat, n + 0 = n := by
  intro n     -- 임의의 n을 고정
  rfl         -- n + 0 = n은 정의에 의해 성립
```

</details>

---

### 연습 4: 존재 한정 증명

"어떤 자연수 n이 존재하여 n * n = 4"임을 증명하라.

```lean
example : ∃ n : Nat, n * n = 4 := by
  sorry
```

<details>
<summary>힌트</summary>

`use`로 n = 2를 제시하면 된다.

</details>

<details>
<summary>정답 보기</summary>

```lean
example : ∃ n : Nat, n * n = 4 := by
  use 2       -- n = 2 선택
  rfl         -- 2 * 2 = 4
```

</details>

---

### 연습 5: 한정기호 부정 (드 모르간)

¬∀x P(x) ↔ ∃x ¬P(x)를 증명하라.

```lean
example (P : α → Prop) : (¬∀ x, P x) ↔ (∃ x, ¬P x) := by
  constructor
  · -- 순방향: ¬∀x P(x) → ∃x ¬P(x)
    intro h
    sorry
  · -- 역방향: ∃x ¬P(x) → ¬∀x P(x)
    intro ⟨x, hx⟩
    intro hall
    sorry
```

<details>
<summary>힌트</summary>

순방향은 `by_contra`와 `push_neg`를 사용한다. 역방향은 `hall x`로 P x를 얻고 `hx`와 모순을 만든다.

</details>

<details>
<summary>정답 보기</summary>

```lean
example (P : α → Prop) : (¬∀ x, P x) ↔ (∃ x, ¬P x) := by
  constructor
  · -- 순방향: ¬∀x P(x) → ∃x ¬P(x)
    intro h
    by_contra h'
    push_neg at h'   -- h' : ∀ x, P x
    exact h h'
  · -- 역방향: ∃x ¬P(x) → ¬∀x P(x)
    intro ⟨x, hx⟩
    intro hall
    exact hx (hall x)  -- hall x : P x, hx : ¬P x → 모순
```

</details>

---

### 연습 6: 한정기호 부정 (드 모르간 2)

¬∃x P(x) ↔ ∀x ¬P(x)를 증명하라.

```lean
example (P : α → Prop) : (¬∃ x, P x) ↔ (∀ x, ¬P x) := by
  constructor
  · -- ¬∃x P(x) → ∀x ¬P(x)
    intro h x hpx
    sorry
  · -- ∀x ¬P(x) → ¬∃x P(x)
    intro h ⟨x, hpx⟩
    sorry
```

<details>
<summary>정답 보기</summary>

```lean
example (P : α → Prop) : (¬∃ x, P x) ↔ (∀ x, ¬P x) := by
  constructor
  · -- ¬∃x P(x) → ∀x ¬P(x)
    intro h x hpx
    exact h ⟨x, hpx⟩   -- ∃x P(x)를 만들어서 h에 적용
  · -- ∀x ¬P(x) → ¬∃x P(x)
    intro h ⟨x, hpx⟩
    exact h x hpx      -- h x : ¬P x, hpx : P x → 모순
```

</details>

---

### 연습 7: 중첩 한정기호 (∀∀)

∀x∀y P(x,y) → ∀y∀x P(x,y)를 증명하라.

```lean
example (P : α → β → Prop) : (∀ x y, P x y) → (∀ y x, P x y) := by
  sorry
```

<details>
<summary>정답 보기</summary>

```lean
example (P : α → β → Prop) : (∀ x y, P x y) → (∀ y x, P x y) := by
  intro h y x
  exact h x y
```

</details>

---

### 연습 8: 중첩 한정기호 (∃∃)

∃x∃y P(x,y) → ∃y∃x P(x,y)를 증명하라.

```lean
example (P : α → β → Prop) : (∃ x y, P x y) → (∃ y x, P x y) := by
  sorry
```

<details>
<summary>정답 보기</summary>

```lean
example (P : α → β → Prop) : (∃ x y, P x y) → (∃ y x, P x y) := by
  intro ⟨x, y, h⟩
  exact ⟨y, x, h⟩
```

</details>

---

### 연습 9: 중첩 한정기호 (∃∀ → ∀∃)

∃y∀x P(x,y) → ∀x∃y P(x,y)를 증명하라.

```lean
example (P : α → β → Prop) : (∃ y, ∀ x, P x y) → (∀ x, ∃ y, P x y) := by
  sorry
```

<details>
<summary>힌트</summary>

`∃ y, ∀ x, P x y`는 "모든 x에 대해 작동하는 하나의 y"를 제공한다. 이를 분해해서 각 x에 대해 같은 y를 제시하면 된다.

</details>

<details>
<summary>정답 보기</summary>

```lean
example (P : α → β → Prop) : (∃ y, ∀ x, P x y) → (∀ x, ∃ y, P x y) := by
  intro ⟨y, h⟩ x   -- y : β, h : ∀ x, P x y, x : α
  exact ⟨y, h x⟩   -- 같은 y를 사용, h x : P x y
```

</details>

---

### 연습 10: 덧셈의 교환법칙

모든 정수 x, y에 대해 x + y = y + x임을 증명하라.

```lean
example : ∀ x y : Int, x + y = y + x := by
  sorry
```

<details>
<summary>정답 보기</summary>

```lean
example : ∀ x y : Int, x + y = y + x := by
  intro x y
  ring
```

</details>

---

### 연습 11: 덧셈에 대한 역원 존재

모든 정수 x에 대해 x + y = 0인 y가 존재함을 증명하라.

```lean
example : ∀ x : Int, ∃ y : Int, x + y = 0 := by
  sorry
```

<details>
<summary>정답 보기</summary>

```lean
example : ∀ x : Int, ∃ y : Int, x + y = 0 := by
  intro x
  use -x
  ring
```

</details>

---

### 연습 12: 전칭 한정과 함축의 결합

(∀ x, P x → Q x) → (∀ x, P x) → (∀ x, Q x)를 증명하라.

```lean
example (P Q : α → Prop) : (∀ x, P x → Q x) → (∀ x, P x) → (∀ x, Q x) := by
  sorry
```

<details>
<summary>힌트</summary>

세 개의 가정을 `intro`로 받고, 첫 번째와 두 번째 가정을 조합한다.

</details>

<details>
<summary>정답 보기</summary>

```lean
example (P Q : α → Prop) : (∀ x, P x → Q x) → (∀ x, P x) → (∀ x, Q x) := by
  intro h1 h2 x
  exact h1 x (h2 x)
```

</details>

---

### 연습 13: 존재 한정과 함축의 결합

(∃ x, P x ∧ Q x) → (∃ x, P x) ∧ (∃ x, Q x)를 증명하라.

```lean
example (P Q : α → Prop) : (∃ x, P x ∧ Q x) → (∃ x, P x) ∧ (∃ x, Q x) := by
  sorry
```

<details>
<summary>힌트</summary>

존재 한정을 분해하여 같은 x에서 P x와 Q x를 얻고, 이를 사용해 두 존재 한정을 만든다.

</details>

<details>
<summary>정답 보기</summary>

```lean
example (P Q : α → Prop) : (∃ x, P x ∧ Q x) → (∃ x, P x) ∧ (∃ x, Q x) := by
  intro ⟨x, hpx, hqx⟩
  constructor
  · exact ⟨x, hpx⟩
  · exact ⟨x, hqx⟩
```

</details>

---

### 연습 14: 전칭 한정 분배 (논리곱)

(∀ x, P x ∧ Q x) ↔ (∀ x, P x) ∧ (∀ x, Q x)를 증명하라.

```lean
example (P Q : α → Prop) : (∀ x, P x ∧ Q x) ↔ (∀ x, P x) ∧ (∀ x, Q x) := by
  constructor
  · -- →
    intro h
    sorry
  · -- ←
    intro ⟨hp, hq⟩ x
    sorry
```

<details>
<summary>정답 보기</summary>

```lean
example (P Q : α → Prop) : (∀ x, P x ∧ Q x) ↔ (∀ x, P x) ∧ (∀ x, Q x) := by
  constructor
  · -- →: (∀ x, P x ∧ Q x) → (∀ x, P x) ∧ (∀ x, Q x)
    intro h
    constructor
    · intro x; exact (h x).left
    · intro x; exact (h x).right
  · -- ←: (∀ x, P x) ∧ (∀ x, Q x) → (∀ x, P x ∧ Q x)
    intro ⟨hp, hq⟩ x
    exact ⟨hp x, hq x⟩
```

</details>

---

### 연습 15: 존재 한정 분배 (논리합)

(∃ x, P x ∨ Q x) ↔ (∃ x, P x) ∨ (∃ x, Q x)를 증명하라.

```lean
example (P Q : α → Prop) : (∃ x, P x ∨ Q x) ↔ (∃ x, P x) ∨ (∃ x, Q x) := by
  constructor
  · -- →
    intro ⟨x, h⟩
    cases h with
    | inl hp => sorry
    | inr hq => sorry
  · -- ←
    intro h
    cases h with
    | inl ⟨x, hp⟩ => sorry
    | inr ⟨x, hq⟩ => sorry
```

<details>
<summary>정답 보기</summary>

```lean
example (P Q : α → Prop) : (∃ x, P x ∨ Q x) ↔ (∃ x, P x) ∨ (∃ x, Q x) := by
  constructor
  · -- →
    intro ⟨x, h⟩
    cases h with
    | inl hp => left; exact ⟨x, hp⟩
    | inr hq => right; exact ⟨x, hq⟩
  · -- ←
    intro h
    cases h with
    | inl ⟨x, hp⟩ => exact ⟨x, Or.inl hp⟩
    | inr ⟨x, hq⟩ => exact ⟨x, Or.inr hq⟩
```

</details>

---

### 연습 16: 중첩 한정기호 부정

push_neg를 사용하여 다음을 증명하라.

```lean
-- ¬∀x∃y P(x,y) ↔ ∃x∀y ¬P(x,y)
example (P : α → β → Prop) : (¬∀ x, ∃ y, P x y) ↔ (∃ x, ∀ y, ¬P x y) := by
  sorry
```

<details>
<summary>정답 보기</summary>

```lean
example (P : α → β → Prop) : (¬∀ x, ∃ y, P x y) ↔ (∃ x, ∀ y, ¬P x y) := by
  push_neg
```

</details>

---

### 연습 17: 제곱이 양수인 수 존재

0이 아닌 정수의 제곱은 양수임을 이용하여, 제곱이 0보다 큰 정수가 존재함을 증명하라.

```lean
example : ∃ n : Int, n * n > 0 := by
  sorry
```

<details>
<summary>정답 보기</summary>

```lean
example : ∃ n : Int, n * n > 0 := by
  use 1
  omega
```

</details>

---

### 연습 18: 곱셈에 대한 항등원

모든 정수 n에 대해 1 * n = n임을 증명하라.

```lean
example : ∀ n : Int, 1 * n = n := by
  sorry
```

<details>
<summary>정답 보기</summary>

```lean
example : ∀ n : Int, 1 * n = n := by
  intro n
  ring
```

</details>

---

## 4-3.9 도전 문제

### 도전 1: 역방향 불성립의 반례

∀x∃y P(x,y)가 참이지만 ∃y∀x P(x,y)가 거짓인 구체적인 예를 Lean4로 표현하라.

```lean
-- P(x, y) = "x + y = 0" 으로 정의
-- ∀x∃y(x + y = 0)은 참 (y = -x 선택)
-- ∃y∀x(x + y = 0)은 거짓 (어떤 y를 골라도 x = -y + 1을 대입하면 거짓)

-- 힌트: 아래 두 정리를 모두 증명하라
example : ∀ x : Int, ∃ y : Int, x + y = 0 := by
  sorry

example : ¬∃ y : Int, ∀ x : Int, x + y = 0 := by
  sorry
```

<details>
<summary>정답 보기</summary>

```lean
-- ∀x∃y(x + y = 0)은 참
example : ∀ x : Int, ∃ y : Int, x + y = 0 := by
  intro x
  use -x
  ring

-- ∃y∀x(x + y = 0)은 거짓
example : ¬∃ y : Int, ∀ x : Int, x + y = 0 := by
  intro ⟨y, h⟩
  have h0 := h 0        -- 0 + y = 0 → y = 0
  have h1 := h 1        -- 1 + y = 0 → y = -1
  omega                 -- y = 0과 y = -1은 모순
```

</details>

---

### 도전 2: 유일 한정기호

∃!x P(x)는 "P(x)를 만족하는 유일한 x가 존재한다"를 의미한다.  
정의: ∃!x P(x) ≡ ∃x(P(x) ∧ ∀y(P(y) → y = x))

Lean4에서 이 정의를 사용하여 "0은 유일한 덧셈 항등원"임을 증명하라.

```lean
-- 힌트: Lean4에서 ∃! 는 ExistsUnique로 표현
-- ∃!x, P x 는 ∃ x, P x ∧ ∀ y, P y → y = x 와 동치

example : ∃! n : Int, ∀ m : Int, m + n = m := by
  sorry
```

<details>
<summary>정답 보기</summary>

```lean
example : ∃! n : Int, ∀ m : Int, m + n = m := by
  use 0
  constructor
  · -- ∀ m, m + 0 = m
    intro m
    ring
  · -- ∀ n', (∀ m, m + n' = m) → n' = 0
    intro n' h
    have := h 0   -- 0 + n' = 0
    omega
```

</details>

---

### 도전 3: 루이스 캐럴의 논증 (예제 26)

다음 세 문장을 한정기호를 사용하여 표현하고, 세 번째가 첫째와 둘째의 정당한 결론임을 증명하라.

1. "All lions are fierce." (모든 사자는 사납다)
2. "Some lions do not drink coffee." (어떤 사자는 커피를 마시지 않는다)  
3. "Some fierce creatures do not drink coffee." (어떤 사나운 생물은 커피를 마시지 않는다)

```lean
-- P(x): x is a lion
-- Q(x): x is fierce
-- R(x): x drinks coffee

example (P Q R : α → Prop) 
  (h1 : ∀ x, P x → Q x)           -- All lions are fierce
  (h2 : ∃ x, P x ∧ ¬R x)          -- Some lions do not drink coffee
  : ∃ x, Q x ∧ ¬R x :=            -- Some fierce creatures do not drink coffee
by
  sorry
```

<details>
<summary>정답 보기</summary>

```lean
example (P Q R : α → Prop) 
  (h1 : ∀ x, P x → Q x)           -- All lions are fierce
  (h2 : ∃ x, P x ∧ ¬R x)          -- Some lions do not drink coffee
  : ∃ x, Q x ∧ ¬R x :=            -- Some fierce creatures do not drink coffee
by
  rcases h2 with ⟨x, hPx, hnotRx⟩  -- x는 사자이고 커피를 안 마신다
  use x
  constructor
  · exact h1 x hPx                 -- x는 사자이므로 사납다
  · exact hnotRx                   -- x는 커피를 안 마신다
```

</details>

---

## 4-3.10 핵심 정리표

### 한정기호 기본

| 기호 | 읽는 법 | 참인 조건 | 거짓인 조건 |
|------|--------|---------|-----------|
| ∀x P(x) | 모든 x에 대해 P(x) | 정의역의 모든 x에 대해 P(x) 참 | P(x)가 거짓인 x 존재 |
| ∃x P(x) | 어떤 x에 대해 P(x) | P(x)가 참인 x가 존재 | 모든 x에 대해 P(x) 거짓 |

### 한정기호 부정 (드 모르간 법칙)

| 부정 | 동치 표현 |
|------|---------|
| ¬∀x P(x) | ∃x ¬P(x) |
| ¬∃x P(x) | ∀x ¬P(x) |

### 중첩 한정기호

| 성질 | 설명 |
|------|------|
| ∀x∀y ≡ ∀y∀x | 같은 종류 한정기호는 순서 교환 가능 |
| ∃x∃y ≡ ∃y∃x | 같은 종류 한정기호는 순서 교환 가능 |
| ∃y∀x → ∀x∃y | 성립 (한 y가 모든 x에 작동하면, 각 x에 y 존재) |
| ∀x∃y → ∃y∀x | 일반적으로 **불성립** |

### Lean4 전술 요약

| 전술 | 목표/가정 | 효과 |
|------|---------|------|
| `intro x` | 목표: `∀ x, P x` | x를 가정에 추가 |
| `use t` | 목표: `∃ x, P x` | x = t 대입 |
| `rcases h with ⟨x, hx⟩` | 가정 h: `∃ x, P x` | x와 hx 추출 |
| `push_neg` | 부정 포함 | 부정을 안쪽으로 |
| `specialize h t` | 가정 h: `∀ x, P x` | h를 P t로 특수화 |

---

## 4-3.11 다음 단계

이제 술어 논리와 한정기호의 기초를 마스터했다! 다음 단계에서는:

1. **추론 규칙**(Rules of Inference): 전칭 예화, 전칭 일반화, 존재 예화, 존재 일반화
2. **증명 전략**: 직접 증명, 대우 증명, 귀류법, 존재 증명
3. **수학적 귀납법**: 자연수에 대한 증명 기법

을 학습할 것이다.

---

*끝*
