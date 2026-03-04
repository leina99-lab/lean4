# Lean4 완전 정복 가이드 —  Part 12-H: 부분순서 — 심화편 (Partial Orders — Advanced)

> **Rosen 이산수학 8판 · Section 9.6 기반**
> 『Mathematics in Lean』 + Lean 4 공식화

---

## 0. 들어가며: 이 파트에서 배울 것

Part 12-G에서 부분순서의 기본 개념(정의, 비교가능성, 전체순서, 하세도표)을 배웠다. 이번에는 부분순서집합 내에서 **특별한 원소들**을 찾고, **격자**(lattice)를 탐구하며, **위상정렬**(topological sort)을 배운다.

### 이 파트의 구성

| 섹션 | 내용 |
|------|------|
| 1 | **극대원소와 극소원소** — maximal, minimal |
| 2 | **최대원소와 최소원소** — greatest, least |
| 3 | **상한과 하한** — upper bound, lower bound |
| 4 | **최소상한계와 최대하한계** — lub, glb |
| 5 | **격자** — lattice: ⊓과 ⊔ |
| 6 | **분배 격자와 흡수 법칙** |
| 7 | **위상정렬** — topological sorting |
| 8 | **종합 연습문제** |

---

## 1. 극대원소와 극소원소 (Maximal and Minimal Elements)

### 1.1 직관적 이해

하세 도표를 떠올려 보자. 하세 도표에서 **꼭대기에 있는 원소들**(위로 더 올라갈 곳이 없는 원소)이 **극대원소**(maximal element)이고, **바닥에 있는 원소들**(아래로 더 내려갈 곳이 없는 원소)이 **극소원소**(minimal element)이다.

### 1.2 형식적 정의

> 부분순서집합 (S, ≼)에서, a < b인 b ∈ S가 없다면 a는 **극대**(maximal)이다. 즉, a보다 **진짜로 큰** 원소가 하나도 없다.

> 비슷하게, b < a인 b ∈ S가 없다면 a는 **극소**(minimal)이다. 즉, a보다 **진짜로 작은** 원소가 하나도 없다.

**중요**: 극대원소는 여러 개 있을 수 있다! "유일한 꼭대기"가 아니라 "더 올라갈 곳이 없는 꼭대기들"이다.

### 예제 14: 나누기 관계에서의 극대/극소원소

> 부분순서집합 ({2, 4, 5, 10, 12, 20, 25}, |)의 극대원소와 극소원소는 무엇인가?

하세도표:
```
   12    20    25
    |   / \    |
    4  10  \   |
    | / \   \  |
    2    5----5
```

**풀이**: 극대원소는 **12, 20, 25**이다 — 이들을 나누는 집합 내의 더 큰 수가 없다. 극소원소는 **2, 5**이다 — 이들이 나누는 집합 내의 더 작은 수가 없다. ◀

이처럼 부분순서집합에는 **둘 이상의 극대원소**와 **둘 이상의 극소원소**가 있을 수 있다.

```lean
-- 극대원소의 형식적 정의
def IsMaximalIn [Preorder α] (S : Set α) (a : α) : Prop :=
  a ∈ S ∧ ∀ b ∈ S, a ≤ b → a = b

-- 극소원소의 형식적 정의
def IsMinimalIn [Preorder α] (S : Set α) (a : α) : Prop :=
  a ∈ S ∧ ∀ b ∈ S, b ≤ a → b = a
```

---

## 2. 최대원소와 최소원소 (Greatest and Least Elements)

### 2.1 극대 vs 최대: 핵심 차이

이 구분은 매우 중요하다!

| | **극대**(maximal) | **최대**(greatest) |
|---|---|---|
| 정의 | 나보다 **진짜로 큰** 원소가 없다 | **모든** 원소가 나보다 작거나 같다 |
| 유일성 | 여러 개 가능 | 있다면 **반드시 유일** |
| 비교 | 비교불가능한 원소 허용 | 모든 원소와 비교가능해야 |

**비유**: 학교에서 수학, 영어, 과학 세 과목의 점수로 학생들을 비교한다고 하자 (사전식 순서 아님, 모든 과목 동시 비교).
- **극대원소**: "모든 과목에서 나보다 높은 학생이 없다" (다른 학생이 나와 비교불가능할 수 있다)
- **최대원소**: "모든 과목에서 내가 모든 학생보다 높거나 같다" (이런 학생은 있기 어렵다!)

### 2.2 형식적 정의

> 모든 b ∈ S에 대해 b ≼ a이면 a는 부분순서집합 (S, ≼)의 **최대원소**(greatest element)이다.

> 모든 b ∈ S에 대해 a ≼ b이면 a는 부분순서집합 (S, ≼)의 **최소원소**(least element)이다.

**최대원소와 최소원소는 존재하면 유일하다!** 이것은 반대칭성에서 바로 나온다: 최대원소가 a, a' 두 개라면 a ≼ a'이고 a' ≼ a이므로 a = a'.

```lean
-- 최대원소의 형식적 정의
def IsGreatestIn [Preorder α] (S : Set α) (a : α) : Prop :=
  a ∈ S ∧ ∀ b ∈ S, b ≤ a

-- 최소원소의 형식적 정의
def IsLeastIn [Preorder α] (S : Set α) (a : α) : Prop :=
  a ∈ S ∧ ∀ b ∈ S, a ≤ b
```

### 예제 15: 최대/최소원소 판정

하세도표를 보고 판정하자:

```
(a)  b   c  d     (b)  d         (c)   d          (d)   d
      \ | /        / \  없음         |              / \
       a          c   없음       b   c             a   b, c 연결
                  |             \ /
                  a  b           a
```

**풀이**:
- (a): 최소원소는 a이다. 최대원소가 **없다** (b, c, d 중 어느 것도 다른 모두보다 크지 않다).
- (b): 최소원소도 최대원소도 **없다**.
- (c): 최소원소가 없다. 최대원소는 d이다.
- (d): 최소원소 a와 최대원소 d가 있다. ◀

### 예제 16: 멱집합의 최대/최소원소

> S가 집합이라 하자. 부분순서집합 (P(S), ⊆)에 최대원소와 최소원소가 있는지 판정하라.

**풀이**: **최소원소는 ∅**이다 — S의 모든 부분집합 T에 대해 ∅ ⊆ T이기 때문이다. **최대원소는 S**이다 — T가 S의 부분집합이면 항상 T ⊆ S이기 때문이다. ◀

### 예제 17: (ℤ⁺, |)의 최대/최소원소

> 부분순서집합 (ℤ⁺, |)에 최대원소와 최소원소가 있는가?

**풀이**: 정수 **1이 최소원소**인데, n이 양의 정수이면 항상 1|n이기 때문이다. **최대원소는 없다** — 모든 양의 정수에 의해 나누어지는 정수가 없기 때문이다. ◀

```lean
-- ℕ에서 0은 ≤에 대한 최소원소이다
example (n : ℕ) : 0 ≤ n := Nat.zero_le n

-- Lean 4에서 OrderBot은 최소원소(⊥)가 있는 구조이다
#check @bot_le ℕ _ _  -- ⊥ ≤ a (ℕ에서 ⊥ = 0)

-- OrderTop은 최대원소(⊤)가 있는 구조
-- ℕ에는 OrderTop이 없다! (최대 자연수가 없으므로)
```

---

## 3. 상한과 하한 (Upper and Lower Bounds)

### 3.1 정의

> u가 S의 원소이고 모든 a ∈ A에 대해 a ≼ u이면, u를 A의 **상한계**(upper bound)라고 부른다.

> l이 S의 원소이고 모든 a ∈ A에 대해 l ≼ a이면, l를 A의 **하한계**(lower bound)라고 부른다.

**주의**: 상한/하한은 반드시 A의 원소일 필요가 없다! S의 원소이면 된다. 예를 들어, 집합 {3, 5}의 상한 중 15는 {3, 5}에 속하지 않지만 상한이다 (나누기 관계에서).

### 예제 18: 하세도표에서의 상한/하한

```
      h
     / \
    g   j
   /|   |
  d   e  f
  | \ / \|
  b   c
   \ /
    a
```

> 부분집합 {a, b, c}의 상한계와 하한계를 구하라.

**풀이**: {a, b, c}의 상한계는 **e, f, j, h**이다 — 이들은 a, b, c 모두보다 크거나 같다. 하한계는 **a**이다 — a는 a, b, c 모두보다 작거나 같다.

> {j, h}의 상한계와 하한계를 구하라.

**풀이**: {j, h}의 상한계는 **없다** — j와 h 모두보다 크거나 같은 원소가 없다. 하한계는 **a, b, c, d, e, f**이다. ◀

> {a, c, d, f}의 상한계와 하한계를 구하라.

**풀이**: {a, c, d, f}의 상한계는 **f, h, j**이고 하한계는 **a**이다. ◀

---

## 4. 최소상한계와 최대하한계 (LUB and GLB)

### 4.1 정의

> 원소 x가 부분집합 A의 **상한계**이면서, A의 **다른 모든 상한계보다 작거나 같으면**, x는 A의 **최소상한계**(least upper bound, lub)이다.

> 원소 y가 부분집합 A의 **하한계**이면서, A의 **다른 모든 하한계보다 크거나 같으면**, y는 A의 **최대하한계**(greatest lower bound, glb)이다.

최소상한계와 최대하한계는 만약 존재하면 **유일**하다!

### 4.2 용어 사전 (매우 중요!)

| 기호 | 이름 1 | 이름 2 | 이름 3 | Lean 이름 |
|------|-------|-------|-------|---------|
| ⊓ | **최대하한계**(glb) | **하한**(infimum) | **만남**(meet) | `inf` |
| ⊔ | **최소상한계**(lub) | **상한**(supremum) | **합류**(join) | `sup` |

VS Code에서의 입력: ⊓는 `\glb`로, ⊔는 `\lub`로 입력한다.

### 예제 19: 하세도표에서 glb와 lub 찾기

```
      h
     / \
    g   j
   /|   |
  d   e  f
  | \ / \|
  b   c
   \ /
    a
```

> {b, d, g}의 최대하한계와 최소상한계가 만약 존재한다면 이름을 구하라.

**풀이**: {b, d, g}의 상한계는 g와 h이다. g < h이므로, g는 **최소상한계**이다. {b, d, g}의 하한계는 a와 b이다. a < b이므로, b는 **최대하한계**이다. ◀

### 예제 20: (ℤ⁺, |)에서의 glb와 lub

> 부분순서집합 (ℤ⁺, |)에서 {3, 9, 12}와 {1, 2, 4, 5, 10}의 최대하한계와 최소상한계를 구하라.

**풀이**:
- {3, 9, 12}의 하한계: 3, 9, 12를 모두 나누는 수 → 1과 3. 최대하한계 = **gcd(3, 9, 12) = 3**.
- {3, 9, 12}의 상한계: 3, 9, 12가 모두 나누는 수 → 36의 배수. 최소상한계 = **lcm(3, 9, 12) = 36**.
- {1, 2, 4, 5, 10}의 최대하한계 = **gcd(1,2,4,5,10) = 1**.
- {1, 2, 4, 5, 10}의 최소상한계 = **lcm(1,2,4,5,10) = 20**. ◀

**핵심 통찰**: (ℤ⁺, |)에서 **glb = gcd**, **lub = lcm**이다!

```lean
-- gcd와 lcm이 나누기 관계에서의 glb/lub
#check Nat.gcd  -- 최대공약수 = 나누기 관계의 glb
#check Nat.lcm  -- 최소공배수 = 나누기 관계의 lub

-- gcd의 핵심 성질
variable (a b : ℕ)
#check (Nat.gcd_dvd_left a b : Nat.gcd a b ∣ a)   -- gcd | a
#check (Nat.gcd_dvd_right a b : Nat.gcd a b ∣ b)  -- gcd | b

-- lcm의 핵심 성질  
#check (Nat.dvd_lcm_left a b : a ∣ Nat.lcm a b)   -- a | lcm
#check (Nat.dvd_lcm_right a b : b ∣ Nat.lcm a b)  -- b | lcm

-- 구체적 계산
example : Nat.gcd 12 18 = 6 := by native_decide
example : Nat.lcm 12 18 = 36 := by native_decide
```

---

## 5. 격자 (Lattice)

### 5.1 정의

> 원소의 **모든 쌍**이 최대하한계와 최소상한계를 갖는 부분순서집합을 **격자**(lattice)라고 부른다.

쉽게 말해: **격자** = 부분순서집합 + "아무 두 원소를 골라도 inf와 sup가 존재한다"

### 5.2 격자의 예

**격자인 것들**:
- **(ℤ, ≤)**: inf(a,b) = min(a,b), sup(a,b) = max(a,b) → 격자 ✓
- **(P(S), ⊆)**: inf(A,B) = A ∩ B, sup(A,B) = A ∪ B → 격자 ✓
- **(ℤ⁺, |)**: inf(a,b) = gcd(a,b), sup(a,b) = lcm(a,b) → 격자 ✓
- **({1, 2, 4, 8, 16}, |)**: 모든 두 원소의 gcd와 lcm이 집합 안에 있다 → 격자 ✓

**격자가 아닌 것**:
- **({1, 2, 3, 4, 5}, |)**: 2와 3의 lcm = 6인데 6 ∉ {1,2,3,4,5} → 격자 ✗

### 예제 22: (ℤ⁺, |)는 격자인가?

> **풀이**: a와 b가 양의 정수라 하자. 이 두 정수의 최소상한계와 최대하한계는 각각 두 정수의 최소공배수와 최대 공약수인데, 독자는 이를 증명해야 한다. 따라서 이 부분순서집합은 격자이다. ◀

### 예제 23: {1, 2, 3, 4, 5}는 격자가 아님

> **풀이**: 2와 3은 ({1, 2, 3, 4, 5}, |)에서 상한계가 없기 때문에 확실하게 최소상한계도 없다. 따라서 첫 번째 부분순서집합은 격자가 아니다. ◀

### 예제 24: 멱집합은 항상 격자

> S가 집합일 때 (P(S), ⊆)가 격자인지 판정하라.

**풀이**: A와 B가 S의 두 부분집합이라 하자. A와 B의 최소상한계와 최대하한계는 각각 **A ∪ B**와 **A ∩ B**인데, 독자는 이를 증명해야 한다. 따라서 (P(S), ⊆)는 격자이다. ◀

### 5.3 Lean 4에서의 격자

```lean
-- Lean 4에서 Lattice 타입 클래스
variable {α : Type*} [Lattice α]
variable (x y z : α)

-- === ⊓ (inf, meet, glb) 의 세 가지 공리 ===
#check (inf_le_left : x ⊓ y ≤ x)             -- inf는 x보다 작거나 같다
#check (inf_le_right : x ⊓ y ≤ y)            -- inf는 y보다 작거나 같다
#check (le_inf : z ≤ x → z ≤ y → z ≤ x ⊓ y) -- z가 x,y 이하이면 inf 이하

-- === ⊔ (sup, join, lub) 의 세 가지 공리 ===
#check (le_sup_left : x ≤ x ⊔ y)             -- x는 sup보다 작거나 같다
#check (le_sup_right : y ≤ x ⊔ y)            -- y는 sup보다 작거나 같다
#check (sup_le : x ≤ z → y ≤ z → x ⊔ y ≤ z) -- x,y가 z 이하이면 sup도 z 이하
```

### 5.4 격자의 핵심 성질들

격자에서 다음 성질들이 성립한다:

```lean
variable {α : Type*} [Lattice α] (x y z : α)

-- 교환법칙 (commutativity)
#check (inf_comm : x ⊓ y = y ⊓ x)
#check (sup_comm : x ⊔ y = y ⊔ x)

-- 결합법칙 (associativity)
#check (inf_assoc : x ⊓ y ⊓ z = x ⊓ (y ⊓ z))
#check (sup_assoc : x ⊔ y ⊔ z = x ⊔ (y ⊔ z))

-- 멱등법칙 (idempotency)
-- x ⊓ x = x, x ⊔ x = x
#check (inf_idem : x ⊓ x = x)
#check (sup_idem : x ⊔ x = x)
```

### 5.5 흡수 법칙 (Absorption Laws)

격자의 가장 특이한 성질 중 하나가 **흡수 법칙**(absorption law)이다:

> x ⊓ (x ⊔ y) = x
> x ⊔ (x ⊓ y) = x

직관적으로: "x와 (x 또는 y)의 공통 부분"은 당연히 x이다. "x 또는 (x와 y의 공통 부분)"도 당연히 x이다.

```lean
-- 흡수 법칙
#check (inf_sup_self : x ⊓ (x ⊔ y) = x)    -- x ⊓ (x ⊔ y) = x
#check (sup_inf_self : x ⊔ (x ⊓ y) = x)    -- x ⊔ (x ⊓ y) = x
```

---

## 6. 분배 격자 (Distributive Lattice)

### 6.1 정의

다음 추가 등식을 만족하는 격자를 **분배 격자**(distributive lattice)라고 한다:

> x ⊓ (y ⊔ z) = (x ⊓ y) ⊔ (x ⊓ z) — **inf가 sup 위에 분배**
> x ⊔ (y ⊓ z) = (x ⊔ y) ⊓ (x ⊔ z) — **sup가 inf 위에 분배**

이 두 등식은 사실 **하나가 성립하면 다른 하나도 자동으로 성립**한다!

### 6.2 분배 격자의 예

- **(ℤ, ≤)** — min과 max는 분배법칙을 만족한다 ✓
- **(P(S), ⊆)** — ∩과 ∪는 분배법칙을 만족한다 ✓
- **(ℤ⁺, |)** — gcd와 lcm은 분배법칙을 만족한다 ✓

```lean
-- Lean 4에서 분배 격자
variable {α : Type*} [DistribLattice α]
variable (x y z : α)

#check (inf_sup_left x y z : x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z)
#check (sup_inf_left x y z : x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z))
```

---

## 7. 위상정렬 (Topological Sorting)

### 7.1 동기: 프로젝트 스케줄링

프로젝트가 20개의 다른 작업들로 구성되어 있다고 하자. 어떤 작업들은 다른 작업들이 끝나야 완료할 수 있다. 어떻게 이 작업들의 순서를 정할까?

이 문제를 모델링하기 위해서 a와 b는 작업이고 a를 마쳐야 b를 시작할 수 있다면 a < b인 부분순서를 정하자. 이 프로젝트의 스케줄을 만들려면, 우리는 모든 20개 작업의 순서가 이 부분순서와 **양립할 수 있어야** 한다.

### 7.2 정의

> aRb이면 항상 a ≼ b이면 전체순서 ≼는 부분순서 R과 **양립할 수 있다**(compatible)고 한다. 부분순서로부터 이와 양립할 수 있는 전체순서를 구하는 것을 **위상정렬**(topological sorting)이라고 한다.

### 7.3 보조정리: 유한 부분순서집합의 최소원소 존재

> **보조정리 1**: 모든 유한한 공집합이 아닌 부분순서집합(S, ≼)은 적어도 한 개의 **극소원소**를 갖는다.

**증명**: S의 한 원소 a₀를 선택하자. a₀가 극소가 아니면 a₁ < a₀인 a₁이 존재한다. a₁이 극소가 아니라면 a₂ < a₁인 a₂가 존재한다. 이 과정을 계속하면, aₙ이 극소가 아니라면 aₙ₊₁ < aₙ인 aₙ₊₁이 존재한다. 이 부분순서집합에 유한한 개수의 원소가 있기 때문에, 이 과정은 반드시 극소원소 aₙ에서 끝나야 한다. ◀

### 7.4 위상정렬 알고리즘

```
알고리즘 1  위상 정렬

procedure topological sort ((S, ≼): finite poset)
k := 1
while S ≠ ∅
    aₖ := a minimal element of S  {보조정리 1에 의해 존재}
    S := S − {aₖ}
    k := k + 1
return a₁, a₂, ⋯, aₙ  {a₁, a₂, ..., aₙ is a compatible total ordering of S}
```

**작동 원리**:
1. 현재 남은 원소들 중 **극소원소**를 하나 선택한다
2. 그 원소를 제거한다
3. 남은 원소가 없을 때까지 반복한다
4. 선택한 순서가 바로 전체순서이다

### 예제 26: 위상정렬 실행

> 부분순서집합({1, 2, 4, 5, 12, 20}, |)에 대해 양립할 수 있는 전체순서를 구하라.

**풀이**: 
1. 첫 번째 할 일은 극소원소를 선택하는 것이다. 극소원소는 **1**인데, 1이 유일한 극소원소이기 때문이다.
2. 다음, ({2, 4, 5, 12, 20}, |)의 극소원소를 선택하자. 이 부분순서집합에는 2개의 극소 원소 **2와 5**가 있다. 이 중 **5**를 선택한다고 하자.
3. 남은 원소는 {2, 4, 12, 20}이다. 이 단계에서 극소원소는 **2**밖에 없다.
4. **4**를 선택하는데 ({4, 12, 20}, |)의 극소원소는 4이기 때문이다.
5. 12와 20은 ({12, 20}, |)의 극소원소이고, 어느 것을 골라도 된다. 우리가 **20**을 고르면, 12가 마지막 원소로 남게 된다.

결과인 전체순서: **1 < 5 < 2 < 4 < 20 < 12** ◀

```lean
-- 위상정렬의 핵심 아이디어를 Lean으로
-- "극소원소를 반복적으로 선택"하는 과정

-- Lean의 List.mergeSort는 전체순서를 이미 사용하지만,
-- 부분순서에서 전체순서를 구성하는 것이 위상정렬의 핵심

-- 간단한 예: 나누기 관계를 확장한 전체순서 확인
-- 1 < 5 < 2 < 4 < 20 < 12 가 나누기 관계와 양립하는지 확인
-- 즉, a | b이면 위의 순서에서 a가 b보다 앞에 있어야 한다

-- 1 | 2 ✓ (1은 2 앞)
-- 1 | 4 ✓ (1은 4 앞)
-- 1 | 5 ✓ (1은 5 앞)
-- 2 | 4 ✓ (2는 4 앞)
-- 2 | 12 ✓ (2는 12 앞)
-- 4 | 12 ✓ (4는 12 앞)
-- 4 | 20 ✓ (4는 20 앞)
-- 5 | 20 ✓ (5는 20 앞)
-- 모든 나누기 관계가 보존되었다!
```

### 예제 27: 프로젝트 작업의 위상정렬

> 어떤 컴퓨터회사의 개발 프로젝트는 7가지 작업을 마쳐야 한다. 어떤 작업은 다른 작업들이 끝나야 시작할 수 있다. 작업의 부분순서는 작업 Y가 작업 X가를 마치기 전까지 시작할 수 없다면 작업 X < 작업 Y를 고려하여 작업들에 대한 부분순서를 만든 수 있다.

하세도표:
```
       G
      / \
     D   F
     |   |
     B   E
    / \
   A   C
```

**풀이**: 7가지 작업의 순서는 위상 정렬을 통해 얻을 수 있다. 정렬의 결과인 **A < C < B < E < F < D < G**는 이 작업들에 대해서 한 가지 가능한 순서이다. ◀

---

## 8. 종합 연습문제

### 연습 8.1: inf의 교환법칙 증명 (설명 + skeleton)

**문제**: 격자에서 x ⊓ y = y ⊓ x임을 증명하라.

**힌트**: `le_antisymm`을 사용하라. x ⊓ y ≤ y ⊓ x와 y ⊓ x ≤ x ⊓ y를 각각 보여야 한다. `le_inf`, `inf_le_left`, `inf_le_right`를 사용하라.

```lean
variable {α : Type*} [Lattice α] (x y : α)

example : x ⊓ y = y ⊓ x := by
  apply le_antisymm
  · apply le_inf
    exact ⟨___⟩   -- 빈칸: x ⊓ y ≤ y 를 증명하는 정리
    exact ⟨___⟩   -- 빈칸: x ⊓ y ≤ x 를 증명하는 정리
  · apply le_inf
    exact ⟨___⟩
    exact ⟨___⟩
```

<details>
<summary>📝 답 보기</summary>

```lean
variable {α : Type*} [Lattice α] (x y : α)

example : x ⊓ y = y ⊓ x := by
  apply le_antisymm
  · apply le_inf
    exact inf_le_right
    exact inf_le_left
  · apply le_inf
    exact inf_le_right
    exact inf_le_left
-- 또는 간단히:
example : x ⊓ y = y ⊓ x := inf_comm
```

</details>

### 연습 8.2: sup의 교환법칙 증명 (skeleton)

```lean
variable {α : Type*} [Lattice α] (x y : α)

example : x ⊔ y = y ⊔ x := by
  apply le_antisymm
  · apply sup_le
    exact ⟨___⟩   -- x ≤ y ⊔ x
    exact ⟨___⟩   -- y ≤ y ⊔ x
  · apply sup_le
    exact ⟨___⟩
    exact ⟨___⟩
```

<details>
<summary>📝 답 보기</summary>

```lean
variable {α : Type*} [Lattice α] (x y : α)

example : x ⊔ y = y ⊔ x := by
  apply le_antisymm
  · apply sup_le
    exact le_sup_right
    exact le_sup_left
  · apply sup_le
    exact le_sup_right
    exact le_sup_left
-- 또는:
example : x ⊔ y = y ⊔ x := sup_comm
```

</details>

### 연습 8.3: 흡수 법칙 1 (sorry)

**문제**: x ⊓ (x ⊔ y) = x를 증명하라.

**힌트**: `le_antisymm`을 사용하고, 한쪽은 `inf_le_left`, 다른 쪽은 `le_inf`와 `le_sup_left`를 조합하라.

```lean
variable {α : Type*} [Lattice α] (x y : α)

theorem absorb1 : x ⊓ (x ⊔ y) = x := by
  sorry
```

<details>
<summary>📝 답 보기</summary>

```lean
variable {α : Type*} [Lattice α] (x y : α)

theorem absorb1 : x ⊓ (x ⊔ y) = x := by
  apply le_antisymm
  · exact inf_le_left                        -- x ⊓ (x ⊔ y) ≤ x
  · exact le_inf le_rfl le_sup_left          -- x ≤ x ⊓ (x ⊔ y)
-- 또는:
theorem absorb1' : x ⊓ (x ⊔ y) = x := inf_sup_self
```

</details>

### 연습 8.4: 흡수 법칙 2 (sorry)

**문제**: x ⊔ (x ⊓ y) = x를 증명하라.

```lean
variable {α : Type*} [Lattice α] (x y : α)

theorem absorb2 : x ⊔ (x ⊓ y) = x := by
  sorry
```

<details>
<summary>📝 답 보기</summary>

```lean
variable {α : Type*} [Lattice α] (x y : α)

theorem absorb2 : x ⊔ (x ⊓ y) = x := by
  apply le_antisymm
  · exact sup_le le_rfl inf_le_left          -- x ⊔ (x ⊓ y) ≤ x
  · exact le_sup_left                         -- x ≤ x ⊔ (x ⊓ y)
-- 또는:
theorem absorb2' : x ⊔ (x ⊓ y) = x := sup_inf_self
```

</details>

### 연습 8.5: inf의 결합법칙 (sorry)

**문제**: x ⊓ y ⊓ z = x ⊓ (y ⊓ z)를 증명하라.

**힌트**: `le_antisymm`을 사용한 뒤, 각 방향을 `le_inf`로 분해하고 `inf_le_left`, `inf_le_right`, `le_trans`를 활용하라.

```lean
variable {α : Type*} [Lattice α] (x y z : α)

example : x ⊓ y ⊓ z = x ⊓ (y ⊓ z) := by
  sorry
```

<details>
<summary>📝 답 보기</summary>

```lean
variable {α : Type*} [Lattice α] (x y z : α)

example : x ⊓ y ⊓ z = x ⊓ (y ⊓ z) := by
  apply le_antisymm
  · apply le_inf
    · exact le_trans inf_le_left inf_le_left  -- x ⊓ y ⊓ z ≤ x
    · apply le_inf
      · exact le_trans inf_le_left inf_le_right  -- x ⊓ y ⊓ z ≤ y
      · exact inf_le_right                       -- x ⊓ y ⊓ z ≤ z
  · apply le_inf
    · apply le_inf
      · exact inf_le_left                        -- x ⊓ (y ⊓ z) ≤ x
      · exact le_trans inf_le_right inf_le_left  -- x ⊓ (y ⊓ z) ≤ y
    · exact le_trans inf_le_right inf_le_right   -- x ⊓ (y ⊓ z) ≤ z
-- 또는:
example : x ⊓ y ⊓ z = x ⊓ (y ⊓ z) := inf_assoc
```

</details>

### 연습 8.6: gcd가 나누기의 glb임을 증명 (sorry)

**문제**: gcd(a, b)가 a와 b 모두를 나눔을 증명하라.

```lean
example (a b : ℕ) : Nat.gcd a b ∣ a ∧ Nat.gcd a b ∣ b := by
  sorry
```

<details>
<summary>📝 답 보기</summary>

```lean
example (a b : ℕ) : Nat.gcd a b ∣ a ∧ Nat.gcd a b ∣ b := by
  exact ⟨Nat.gcd_dvd_left a b, Nat.gcd_dvd_right a b⟩
```

</details>

### 연습 8.7: 최대원소의 유일성 증명 (sorry)

**문제**: 부분순서집합에서 최대원소가 존재하면 유일함을 증명하라. (Rosen 연습문제 40(a))

```lean
variable {α : Type*} [PartialOrder α] {S : Set α}

-- 최대원소가 두 개 있다고 가정하면 같음을 보여라
example (a b : α) (ha : a ∈ S ∧ ∀ x ∈ S, x ≤ a) 
    (hb : b ∈ S ∧ ∀ x ∈ S, x ≤ b) : a = b := by
  sorry
```

<details>
<summary>📝 답 보기</summary>

```lean
variable {α : Type*} [PartialOrder α] {S : Set α}

example (a b : α) (ha : a ∈ S ∧ ∀ x ∈ S, x ≤ a) 
    (hb : b ∈ S ∧ ∀ x ∈ S, x ≤ b) : a = b := by
  apply le_antisymm
  · exact hb.2 a ha.1   -- a ≤ b (b는 최대이고 a ∈ S)
  · exact ha.2 b hb.1   -- b ≤ a (a는 최대이고 b ∈ S)
```

</details>

### 연습 8.8: 전체순서에서 두 원소의 inf = min (sorry)

**문제**: 전체순서에서 `min a b ≤ a`임을 증명하라.

```lean
example (a b : ℕ) : min a b ≤ a := by
  sorry
```

<details>
<summary>📝 답 보기</summary>

```lean
example (a b : ℕ) : min a b ≤ a := by
  exact min_le_left a b
-- 또는:
example (a b : ℕ) : min a b ≤ a := by
  omega
```

</details>

### 연습 8.9: 분배 격자 활용 (sorry)

**문제**: 분배 격자에서 x ⊓ (y ⊔ z) = (x ⊓ y) ⊔ (x ⊓ z)임을 증명하라.

```lean
variable {α : Type*} [DistribLattice α] (x y z : α)

example : x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z := by
  sorry
```

<details>
<summary>📝 답 보기</summary>

```lean
variable {α : Type*} [DistribLattice α] (x y z : α)

example : x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z := by
  exact inf_sup_left x y z
```

</details>

### 연습 8.10: gcd의 교환법칙 (sorry)

**문제**: gcd(m, n) = gcd(n, m)임을 증명하라.

```lean
example (m n : ℕ) : Nat.gcd m n = Nat.gcd n m := by
  sorry
```

<details>
<summary>📝 답 보기</summary>

```lean
example (m n : ℕ) : Nat.gcd m n = Nat.gcd n m := by
  exact Nat.gcd_comm m n
```

</details>

### 연습 8.11: 부분순서에서 a < b → b < c → a < c (sorry)

```lean
variable {α : Type*} [PartialOrder α]

example (a b c : α) (h1 : a < b) (h2 : b < c) : a < c := by
  sorry
```

<details>
<summary>📝 답 보기</summary>

```lean
variable {α : Type*} [PartialOrder α]

example (a b c : α) (h1 : a < b) (h2 : b < c) : a < c := by
  exact lt_trans h1 h2
```

</details>

### 연습 8.12: 분배 격자에서 역방향 분배법칙 (sorry)

**문제**: 분배 격자에서 x ⊔ (y ⊓ z) = (x ⊔ y) ⊓ (x ⊔ z)임을 증명하라.

```lean
variable {α : Type*} [DistribLattice α] (x y z : α)

example : x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z) := by
  sorry
```

<details>
<summary>📝 답 보기</summary>

```lean
variable {α : Type*} [DistribLattice α] (x y z : α)

example : x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z) := by
  exact sup_inf_left x y z
```

</details>

---

## 9. 핵심 요약

1. **극대원소**(maximal): 나보다 큰 원소가 없다. 여러 개 가능.
2. **최대원소**(greatest): 모든 원소가 나보다 작거나 같다. 있으면 유일.
3. **극소원소**(minimal): 나보다 작은 원소가 없다. 여러 개 가능.
4. **최소원소**(least): 모든 원소가 나보다 크거나 같다. 있으면 유일.
5. **상한계**(upper bound): 부분집합의 모든 원소보다 큰 원소 (S의 원소).
6. **하한계**(lower bound): 부분집합의 모든 원소보다 작은 원소 (S의 원소).
7. **최소상한계**(lub) = **상한**(sup) = ⊔ = **합류**(join). **최대하한계**(glb) = **하한**(inf) = ⊓ = **만남**(meet).
8. **격자**(lattice): 모든 원소 쌍이 inf와 sup를 갖는 부분순서집합.
9. 격자의 예: (ℤ, ≤)에서 min/max, (P(S), ⊆)에서 ∩/∪, (ℤ⁺, |)에서 gcd/lcm.
10. **흡수 법칙**: x ⊓ (x ⊔ y) = x, x ⊔ (x ⊓ y) = x.
11. **분배 격자**: x ⊓ (y ⊔ z) = (x ⊓ y) ⊔ (x ⊓ z).
12. **위상정렬**: 부분순서에서 양립하는 전체순서를 구하는 알고리즘. 매번 극소원소를 선택하여 제거.
13. **보조정리 1**: 유한한 공집합이 아닌 부분순서집합은 극소원소를 갖는다.

---

## 10. 사용된 Lean 4 전술 정리

| 전술 / 정리 | 용도 | 예시 |
|------|------|------|
| `inf_le_left` | x ⊓ y ≤ x | 격자의 기본 공리 |
| `inf_le_right` | x ⊓ y ≤ y | 격자의 기본 공리 |
| `le_inf` | z ≤ x → z ≤ y → z ≤ x ⊓ y | inf의 최대성 |
| `le_sup_left` | x ≤ x ⊔ y | 격자의 기본 공리 |
| `le_sup_right` | y ≤ x ⊔ y | 격자의 기본 공리 |
| `sup_le` | x ≤ z → y ≤ z → x ⊔ y ≤ z | sup의 최소성 |
| `inf_comm` | x ⊓ y = y ⊓ x | 교환법칙 |
| `sup_comm` | x ⊔ y = y ⊔ x | 교환법칙 |
| `inf_assoc` | 결합법칙 | x ⊓ y ⊓ z = x ⊓ (y ⊓ z) |
| `inf_sup_self` | x ⊓ (x ⊔ y) = x | 흡수법칙 |
| `sup_inf_self` | x ⊔ (x ⊓ y) = x | 흡수법칙 |
| `inf_sup_left` | 분배법칙 | x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z |
| `le_antisymm` | 반대칭성 | 격자 등식 증명의 핵심 전략 |
| `Nat.gcd_dvd_left` | gcd(a,b) ∣ a | gcd 성질 |
| `Nat.gcd_dvd_right` | gcd(a,b) ∣ b | gcd 성질 |

---

> **다음 파트 예고**: Part 13에서는 **그래프 이론**(Graph Theory, Rosen Chapter 10)을 시작한다. 그래프의 정의, 특수 그래프, 이분 그래프, 그래프 모델, 오일러 경로, 해밀턴 경로를 Lean 4로 구현한다!
