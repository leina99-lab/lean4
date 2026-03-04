# Lean4 완전 정복 가이드 —  Part 12-D: 관계의 표현 — 행렬과 방향성 그래프 (Representing Relations)

> **Rosen 이산수학 8판 · Section 9.3 기반**
> 『Mathematics in Lean』 + Lean 4 공식화

---

## 0. 들어가며: 이 파트에서 배울 것

관계를 순서쌍의 목록으로 나열하는 것은 이해하기 쉽지만, 관계가 커지면 관리하기 어려워진다. 이 파트에서는 관계를 표현하는 두 가지 강력한 도구를 배운다:

1. **행렬**(matrix)을 이용한 관계의 표현 — **0-1 행렬**
2. 행렬로 관계의 성질(반사적, 대칭적 등)을 판단하는 방법
3. 관계의 합집합과 교집합의 행렬 표현
4. **부울 곱**(Boolean product)으로 관계의 합성 계산
5. **방향성 그래프**(directed graph, digraph)로 관계 표현하기

### 이 파트에서 사용하는 핵심 Lean 4 개념

| 개념 | 설명 |
|------|------|
| `Fin n → Fin n → ℕ` | n × n 행렬을 함수로 표현 |
| `fin_cases` | Fin n의 모든 경우 나누기 |
| `decide` | 유한 명제의 자동 판정 |
| `List.finRange n` | [0, 1, ..., n-1] 리스트 |
| `List.contains` | 리스트 원소 소속 검사 |

---

## 1. 0-1 행렬로 관계 표현하기

### 1.1 핵심 아이디어

유한집합 사이의 관계는 **0과 1로만 이루어진 행렬**로 표현할 수 있다. 이 아이디어는 놀라울 정도로 단순하고 강력하다!

R을 A = {a₁, a₂, ..., aₘ}에서 B = {b₁, b₂, ..., bₙ}으로의 관계라 하자. (여기서 A와 B의 원소가 특정한, 그러나 임의의 순서로 나열되었다.) 관계 R을 행렬 **M**\_R = [m_{ij}]로 표현할 수 있는데:

```
m_{ij} = 1   (aᵢ, bⱼ) ∈ R이면 (즉, aᵢ와 bⱼ가 관련되면)
m_{ij} = 0   (aᵢ, bⱼ) ∉ R이면 (즉, aᵢ와 bⱼ가 관련되지 않으면)
```

**비유**: 학생과 과목의 수강 관계를 생각해보자. 행은 학생, 열은 과목이다. 학생 i가 과목 j를 수강하면 칸에 1을 쓰고, 아니면 0을 쓴다. 이것이 바로 0-1 행렬이다!

### 1.2 예제 1 (Rosen)

A = {1, 2, 3}이고 B = {1, 2}라고 하자. R이 A에서 B로의 관계로 a ∈ A, b ∈ B, a > b이면 (a, b)를 포함한다.

a₁ = 1, a₂ = 2, a₃ = 3, b₁ = 1, b₂ = 2일 때 R을 표현하는 행렬은?

**풀이**: R = {(2, 1), (3, 1), (3, 2)}이므로

```
      b₁  b₂
a₁ [  0   0 ]    -- 1 > 1? ✗, 1 > 2? ✗
a₂ [  1   0 ]    -- 2 > 1? ✓, 2 > 2? ✗
a₃ [  1   1 ]    -- 3 > 1? ✓, 3 > 2? ✓
```

```lean
-- 예제 1: A = {1,2,3}, B = {1,2}, R: a > b
-- Lean 4에서 0-1 행렬을 함수로 정의
def M_R_ex1 : Fin 3 → Fin 2 → ℕ
  | 0, 0 => 0  | 0, 1 => 0     -- a₁=1: 1>1? ✗, 1>2? ✗
  | 1, 0 => 1  | 1, 1 => 0     -- a₂=2: 2>1? ✓, 2>2? ✗
  | 2, 0 => 1  | 2, 1 => 1     -- a₃=3: 3>1? ✓, 3>2? ✓

-- 확인
#eval M_R_ex1 1 0  -- 1 (= (2,1) ∈ R)
#eval M_R_ex1 0 0  -- 0 (= (1,1) ∉ R)
```

> **Lean 4 설명**: `Fin n`은 0부터 n-1까지의 자연수 타입이다. `Fin 3`은 {0, 1, 2}이다. 여기서 0은 a₁=1에, 1은 a₂=2에, 2는 a₃=3에 대응한다. 행렬을 함수 `Fin m → Fin n → ℕ`로 정의하면, `M i j`로 (i, j) 성분에 접근할 수 있다.

### 1.3 예제 2 (Rosen)

A = {a₁, a₂, a₃}이고 B = {b₁, b₂, b₃, b₄, b₅}라고 하자. 행렬이 다음과 같을 때, 이 표현하는 관계 R에는 어떤 순서쌍이 있는가?

```
M_R = [0 1 0 0 0]
      [1 0 1 1 0]
      [1 0 1 0 1]
```

**풀이**: m_{ij} = 1인 순서쌍 (aᵢ, bⱼ)로 구성되므로:

R = {(a₁, b₂), (a₂, b₁), (a₂, b₃), (a₂, b₄), (a₃, b₁), (a₃, b₃), (a₃, b₅)}

```lean
-- 예제 2: 행렬에서 관계 추출하기
def M_R_ex2 : Fin 3 → Fin 5 → ℕ
  | 0, 0 => 0  | 0, 1 => 1  | 0, 2 => 0  | 0, 3 => 0  | 0, 4 => 0
  | 1, 0 => 1  | 1, 1 => 0  | 1, 2 => 1  | 1, 3 => 1  | 1, 4 => 0
  | 2, 0 => 1  | 2, 1 => 0  | 2, 2 => 1  | 2, 3 => 0  | 2, 4 => 1

-- 행렬에서 관계(순서쌍 리스트) 추출하는 일반 함수
def extractRelation (M : Fin m → Fin n → ℕ) : List (Fin m × Fin n) :=
  List.join <| (List.finRange m).map fun i =>
    ((List.finRange n).filter fun j => M i j == 1).map fun j => (i, j)

#eval extractRelation M_R_ex2
-- [(0,1), (1,0), (1,2), (1,3), (2,0), (2,2), (2,4)]
```

---

## 2. 행렬로 관계의 성질 판단하기

행렬 표현의 진정한 힘은 관계의 **성질**을 행렬의 **패턴**으로 판단할 수 있다는 데 있다!

### 2.1 반사적 관계 (Reflexive)

집합 A에 대한 관계 R은 모든 a ∈ A에 대해 (a, a) ∈ R이면 **반사적**(reflexive)이다.

행렬로 보면: **주 대각선**(main diagonal)의 모든 원소가 1이면 R은 반사적이다.

```
반사적 관계의 행렬:        비반사적 관계의 행렬:
[1  ?  ?  ?]              [0  ?  ?  ?]
[?  1  ?  ?]              [?  1  ?  ?]     ← 대각선에 0이 하나라도 있으면 ✗
[?  ?  1  ?]              [?  ?  1  ?]
[?  ?  ?  1]              [?  ?  ?  1]
```

(대각선 이외의 성분은 0일 수도 1일 수도 있다.)

```lean
-- 반사적 관계: 주 대각선이 모두 1
def isReflexiveMatrix (M : Fin n → Fin n → ℕ) : Prop :=
  ∀ i : Fin n, M i i = 1

-- 예: 항등 행렬은 반사적
def I₃ : Fin 3 → Fin 3 → ℕ
  | 0, 0 => 1  | 0, 1 => 0  | 0, 2 => 0
  | 1, 0 => 0  | 1, 1 => 1  | 1, 2 => 0
  | 2, 0 => 0  | 2, 1 => 0  | 2, 2 => 1

example : isReflexiveMatrix I₃ := by
  intro i
  fin_cases i <;> rfl   -- i = 0, 1, 2 각각에 대해 rfl
```

> **Lean 4 설명**: `fin_cases i`는 `i : Fin 3`일 때, i = 0, i = 1, i = 2의 세 경우로 나눈다. 유한 타입의 **모든 경우를 나열**하는 강력한 전술이다! 각 경우에 `rfl`(정의에 의한 같음)으로 증명이 완료된다.

### 2.2 대칭적 관계 (Symmetric)

관계 R이 **대칭적**(symmetric)이면: (a, b) ∈ R일 때 항상 (b, a) ∈ R이다.

행렬으로 보면: **M\_R이 대칭 행렬**(symmetric matrix)이다. 즉, **M\_R = (M\_R)ᵀ** 이다!

```
대칭적 관계의 행렬:         비대칭적 관계의 행렬:
[1  1  0]                 [1  1  0]
[1  1  1]   M = Mᵀ       [0  1  1]   m₀₁ = 1이지만 m₁₀ = 0 → ✗
[0  1  1]                 [0  1  1]
```

```lean
-- 대칭적 관계: M i j = M j i (모든 i, j에 대해)
def isSymmetricMatrix (M : Fin n → Fin n → ℕ) : Prop :=
  ∀ i j : Fin n, M i j = M j i

-- 예제: 대칭 행렬
def M_sym : Fin 3 → Fin 3 → ℕ
  | 0, 0 => 1  | 0, 1 => 1  | 0, 2 => 0
  | 1, 0 => 1  | 1, 1 => 1  | 1, 2 => 1
  | 2, 0 => 0  | 2, 1 => 1  | 2, 2 => 1

example : isSymmetricMatrix M_sym := by
  intro i j
  fin_cases i <;> fin_cases j <;> rfl
```

> **Lean 4 설명**: `fin_cases i <;> fin_cases j`는 (i, j)의 **모든 조합**을 나열한다. 3×3 행렬이면 9가지 경우를 각각 확인한다. `<;>`는 "앞 전술의 모든 결과 목표에 뒤 전술을 적용"하라는 의미이다.

### 2.3 반대칭적 관계 (Antisymmetric)

관계 R이 **반대칭적**(antisymmetric)이면: (a, b) ∈ R이고 (b, a) ∈ R이면 a = b이다.

행렬으로 보면: i ≠ j이고 m_{ij} = 1이면, m_{ji} = 0이어야 한다. 즉, **대각선 밖에서 1이 서로 마주보지 않는다**.

```
반대칭적 관계의 행렬:
[1  1  0]
[0  1  0]    대각선 밖: m₀₁=1 → m₁₀=0 ✓
[0  1  1]              m₂₁=1 → m₁₂=0 ✓
```

```lean
-- 반대칭적 관계: i ≠ j이고 M i j = 1이면 M j i = 0
def isAntisymmetricMatrix (M : Fin n → Fin n → ℕ) : Prop :=
  ∀ i j : Fin n, i ≠ j → M i j = 1 → M j i = 0
```

### 2.4 예제 3 (Rosen)

어떤 집합에 대한 관계 R이 다음 행렬로 표현되면:

```
M_R = [1 1 0]
      [1 1 1]
      [0 1 1]
```

이 관계 R은 반사적인가? 대칭적인가? 반대칭적인가?

```lean
def M_R_ex3 : Fin 3 → Fin 3 → ℕ
  | 0, 0 => 1  | 0, 1 => 1  | 0, 2 => 0
  | 1, 0 => 1  | 1, 1 => 1  | 1, 2 => 1
  | 2, 0 => 0  | 2, 1 => 1  | 2, 2 => 1

-- ✓ 반사적: 대각선이 모두 1
example : isReflexiveMatrix M_R_ex3 := by
  intro i; fin_cases i <;> rfl

-- ✓ 대칭적: M = Mᵀ
example : isSymmetricMatrix M_R_ex3 := by
  intro i j; fin_cases i <;> fin_cases j <;> rfl

-- ✗ 반대칭적이 아님: m₀₁ = 1이고 m₁₀ = 1인데 0 ≠ 1
example : ¬ isAntisymmetricMatrix M_R_ex3 := by
  intro h
  have := h 0 1 (by omega) rfl
  -- M_R_ex3 1 0 = 0이어야 하는데, 실제로 1
  simp [M_R_ex3] at this
```

---

## 3. 관계의 합집합과 교집합의 행렬

### 3.1 개념

R₁과 R₂가 집합 A에 대한 관계이고, 이를 표현하는 행렬이 각각 **M**_{R₁}과 **M**_{R₂}라고 하자.

- **합집합**의 행렬: **M**_{R₁ ∪ R₂} = **M**_{R₁} ∨ **M**_{R₂}
  - 원소별로 OR 연산: 둘 중 하나라도 1이면 1
- **교집합**의 행렬: **M**_{R₁ ∩ R₂} = **M**_{R₁} ∧ **M**_{R₂}
  - 원소별로 AND 연산: 둘 다 1이어야 1

```lean
-- 합집합 (원소별 OR = max)
def matOr (M₁ M₂ : Fin n → Fin n → ℕ) : Fin n → Fin n → ℕ :=
  fun i j => max (M₁ i j) (M₂ i j)

-- 교집합 (원소별 AND = min)
def matAnd (M₁ M₂ : Fin n → Fin n → ℕ) : Fin n → Fin n → ℕ :=
  fun i j => min (M₁ i j) (M₂ i j)
```

### 3.2 예제 4 (Rosen)

집합 A에 대한 관계 R₁과 R₂가 다음 행렬에 의해 표현된다:

```
M_{R₁} = [1 0 1]    M_{R₂} = [1 0 1]
         [1 0 0]             [0 1 1]
         [0 1 0]             [1 0 0]
```

```lean
def M_R1 : Fin 3 → Fin 3 → ℕ
  | 0, 0 => 1  | 0, 1 => 0  | 0, 2 => 1
  | 1, 0 => 1  | 1, 1 => 0  | 1, 2 => 0
  | 2, 0 => 0  | 2, 1 => 1  | 2, 2 => 0

def M_R2 : Fin 3 → Fin 3 → ℕ
  | 0, 0 => 1  | 0, 1 => 0  | 0, 2 => 1
  | 1, 0 => 0  | 1, 1 => 1  | 1, 2 => 1
  | 2, 0 => 1  | 2, 1 => 0  | 2, 2 => 0

-- 행렬을 보기 좋게 출력하는 함수
def showMatrix (M : Fin n → Fin n → ℕ) : List (List ℕ) :=
  (List.finRange n).map fun i =>
    (List.finRange n).map fun j => M i j

-- 합집합: M_{R₁ ∪ R₂} = [[1,0,1], [1,1,1], [1,1,0]]
#eval showMatrix (matOr M_R1 M_R2)

-- 교집합: M_{R₁ ∩ R₂} = [[1,0,1], [0,0,0], [0,0,0]]
#eval showMatrix (matAnd M_R1 M_R2)
```

---

## 4. 부울 곱과 관계의 합성

### 4.1 부울 곱이란?

관계의 **합성**(composition)을 행렬로 계산하려면 **부울 곱**(Boolean product)이 필요하다. 일반 행렬 곱과 비슷하지만, 덧셈을 OR(∨)로, 곱셈을 AND(∧)로 바꾼 것이다.

**일반 행렬 곱 vs 부울 곱 비교**:

| 연산 | 일반 행렬 곱 | 부울 곱 |
|------|----------|--------|
| 원소 곱 | × (곱셈) | ∧ (AND) |
| 원소 합 | + (덧셈) | ∨ (OR) |
| 결과 | 임의의 수 | 0 또는 1 |

> **수식**: (i, j) 성분 = (r_{i1} ∧ s_{1j}) ∨ (r_{i2} ∧ s_{2j}) ∨ ⋯ ∨ (r_{in} ∧ s_{nj})

쉽게 말해서: "행렬 곱에서 + 대신 OR, × 대신 AND를 사용한다."

그런데 왜 이것이 관계의 합성에 대응할까? S ∘ R의 정의를 떠올려보자:

(a, c) ∈ S ∘ R ⟺ 어떤 b가 존재하여 (a, b) ∈ R **이고** (b, c) ∈ S

- "어떤 b가 존재하여" → OR (∨)로 모든 b를 검사
- "(a, b) ∈ R **이고** (b, c) ∈ S" → AND (∧)로 두 조건 결합

따라서 **부울 곱은 관계의 합성을 정확히 계산한다!**

### 4.2 Lean 4에서의 구현

```lean
-- 부울 곱 (Boolean product)
def boolProd (M₁ : Fin m → Fin n → ℕ) (M₂ : Fin n → Fin p → ℕ) :
    Fin m → Fin p → ℕ :=
  fun i j =>
    if (List.finRange n).any (fun k => M₁ i k == 1 && M₂ k j == 1)
    then 1 else 0
```

### 4.3 예제 5 (Rosen)

R과 S를 표현하는 행렬이 다음과 같을 때, 관계 S ∘ R을 표현하는 행렬을 구하라.

```
M_R = [1 0 1]    M_S = [0 1 0]
      [1 1 0]          [0 0 1]
      [0 0 0]          [1 0 1]
```

**풀이** (부울 곱 M_R ⊙ M_S):

행 0, 열 0: (1∧0) ∨ (0∧0) ∨ (1∧1) = 0 ∨ 0 ∨ 1 = **1**
행 0, 열 1: (1∧1) ∨ (0∧0) ∨ (1∧0) = 1 ∨ 0 ∨ 0 = **1**
행 0, 열 2: (1∧0) ∨ (0∧1) ∨ (1∧1) = 0 ∨ 0 ∨ 1 = **1**
... (나머지도 같은 방식)

```lean
def M_R_5 : Fin 3 → Fin 3 → ℕ
  | 0, 0 => 1  | 0, 1 => 0  | 0, 2 => 1
  | 1, 0 => 1  | 1, 1 => 1  | 1, 2 => 0
  | 2, 0 => 0  | 2, 1 => 0  | 2, 2 => 0

def M_S_5 : Fin 3 → Fin 3 → ℕ
  | 0, 0 => 0  | 0, 1 => 1  | 0, 2 => 0
  | 1, 0 => 0  | 1, 1 => 0  | 1, 2 => 1
  | 2, 0 => 1  | 2, 1 => 0  | 2, 2 => 1

-- S ∘ R의 행렬 = M_R ⊙ M_S
#eval showMatrix (boolProd M_R_5 M_S_5)
-- [[1, 1, 1], [0, 1, 1], [0, 0, 0]]
```

### 4.4 관계의 거듭제곱

R^n (R을 n번 합성)은 행렬의 **부울 거듭제곱**으로 구할 수 있다:

**M**_{Rⁿ} = **M**\_R^{[n]} (부울 곱을 n번 반복)

```lean
-- 부울 거듭제곱
def boolPow (M : Fin n → Fin n → ℕ) : ℕ → Fin n → Fin n → ℕ
  | 0 => fun i j => if i == j then 1 else 0  -- 항등 행렬
  | k + 1 => boolProd (boolPow M k) M

-- 예제 6 (Rosen)
def M_R_6 : Fin 3 → Fin 3 → ℕ
  | 0, 0 => 0  | 0, 1 => 1  | 0, 2 => 0
  | 1, 0 => 0  | 1, 1 => 1  | 1, 2 => 1
  | 2, 0 => 1  | 2, 1 => 0  | 2, 2 => 0

-- R²의 행렬
#eval showMatrix (boolPow M_R_6 2)
-- [[0, 1, 1], [1, 1, 1], [0, 1, 0]]
```

---

## 5. 방향성 그래프로 관계 표현하기

### 5.1 방향성 그래프란?

순서쌍의 목록이나 행렬 외에, 관계를 **그림**으로 표현하는 중요한 방법이 있다.

> **정의 1** (Rosen): **방향성 그래프**(directed graph, digraph)는 **꼭지점**(vertex, node)의 집합 V와 **모서리**(edge, arc)라 불리는 V의 순서쌍 집합 E로 구성된다. 꼭지점 a는 모서리 (a, b)의 **시작점**(initial vertex)이라고 하고, 꼭지점 b는 이 모서리의 **끝점**(terminal vertex)이라고 부른다.

핵심 개념:
- (a, a) 형태의 모서리를 **루프**(loop)라고 부른다 — 자기 자신으로 돌아오는 화살표
- 화살표에는 **방향**이 있다: (a, b)와 (b, a)는 서로 다른 모서리이다
- 집합 A에 대한 관계 R은 곧 방향성 그래프이다: 꼭지점 = A의 원소, 모서리 = R의 순서쌍

**비유**: SNS에서 "팔로우" 관계를 생각하자. "A가 B를 팔로우한다"와 "B가 A를 팔로우한다"는 다르다. 각 사람이 꼭지점이고, 팔로우 관계가 화살표(모서리)이다.

### 5.2 Lean 4에서 방향성 그래프 표현

```lean
-- 방향성 그래프 = 모서리(순서쌍)의 리스트
-- 예제 8 (Rosen): 집합 {1, 2, 3, 4}에 관한 관계
-- R₁ = {(1,1), (1,3), (2,1), (2,3), (2,4), (3,1), (3,2), (4,1)}
-- Fin 4 사용: 원소 1→인덱스 0, 원소 2→인덱스 1, 원소 3→인덱스 2, 원소 4→인덱스 3
def R₁_edges : List (Fin 4 × Fin 4) :=
  [(0,0), (0,2), (1,0), (1,2), (1,3), (2,0), (2,1), (3,0)]

-- 인접 행렬 (adjacency matrix) 생성
def adjMatrix (edges : List (Fin n × Fin n)) : Fin n → Fin n → ℕ :=
  fun i j => if edges.contains (i, j) then 1 else 0

#eval showMatrix (adjMatrix R₁_edges)
-- [[1,0,1,0], [1,0,1,1], [1,1,0,0], [1,0,0,0]]
```

### 5.3 방향성 그래프에서 관계의 성질 읽기

방향성 그래프를 보면 관계의 성질을 **시각적으로** 판단할 수 있다:

| 성질 | 그래프에서의 의미 | 행렬에서의 의미 |
|------|--------------|------------|
| **반사적**(reflexive) | 모든 꼭지점에 루프가 있다 | 대각선 모두 1 |
| **대칭적**(symmetric) | 모든 모서리의 반대 방향도 있다 | M = Mᵀ |
| **반대칭적**(antisymmetric) | 서로 다른 두 꼭지점 사이에 양방향 ✗ | 대각선 밖에서 대칭 1 쌍 없음 |
| **전이적**(transitive) | a→b→c이면 a→c도 있다 | M² ≤ M (부울 곱) |

### 5.4 예제 10 (Rosen)

그림 6의 관계 S₁에 대해 성질을 판정하라.

S₁: 각 꼭지점에 루프가 있고, a→b 모서리가 있지만 b→a는 없고, b→c는 양방향이다.

- **반사적**: 모든 꼭지점에 루프 → ✓
- **대칭적**: a→b인데 b→a 아님 → ✗
- **반대칭적**: b↔c 양방향인데 b≠c → ✗
- **전이적**: a→b, b→c인데 a→c 없음 → ✗

---

## 6. 연습 문제 — 레벨 1: 괄호 채우기

### 연습 6.1: 관계에서 행렬 만들기 (Rosen 연습문제 1a)

{1, 2, 3}에 대한 관계 {(1,1), (1,2), (1,3)}을 행렬로 표현하라.

```lean
def M_6_1 : Fin 3 → Fin 3 → ℕ
  | 0, 0 => /- ? -/  | 0, 1 => /- ? -/  | 0, 2 => /- ? -/
  | 1, 0 => /- ? -/  | 1, 1 => /- ? -/  | 1, 2 => /- ? -/
  | 2, 0 => /- ? -/  | 2, 1 => /- ? -/  | 2, 2 => /- ? -/
```

<details>
<summary>💡 답 보기</summary>

```lean
-- R = {(1,1), (1,2), (1,3)} → 인덱스: {(0,0), (0,1), (0,2)}
def M_6_1 : Fin 3 → Fin 3 → ℕ
  | 0, 0 => 1  | 0, 1 => 1  | 0, 2 => 1
  | 1, 0 => 0  | 1, 1 => 0  | 1, 2 => 0
  | 2, 0 => 0  | 2, 1 => 0  | 2, 2 => 0
```

**설명**: 첫 번째 행(a₁=1)에서만 관계가 있으므로 첫 행만 1이다.
</details>

### 연습 6.2: 행렬에서 관계 읽기 (Rosen 연습문제 3b)

```lean
-- 다음 행렬에 대응하는 관계의 순서쌍을 나열하라 (오름차순)
-- M = [0 1 0]
--     [0 1 0]
--     [0 1 0]
-- R = { /- 여기를 채우세요 -/ }
```

<details>
<summary>💡 답 보기</summary>

R = {(1, 2), (2, 2), (3, 2)}

**설명**: m_{ij} = 1인 위치: (0,1), (1,1), (2,1). 원소로 바꾸면 (1,2), (2,2), (3,2). 모든 원소가 2번 원소와 관련된다.
</details>

### 연습 6.3: 성질 판정 (Rosen 연습문제 7)

```lean
-- 연습문제 3의 행렬로 표현된 관계들이 반사적인지, 비반사적인지,
-- 대칭적인지, 반대칭적인지, 전이적인지 판단하라

-- (b) M = [0 1 0]
--         [0 1 0]
--         [0 1 0]

-- 반사적? 대각선: m₀₀ = 0 → ✗ (반사적 아님)
-- 대칭적? m₀₁ = 1이지만 m₁₀ = 0 → ✗ (대칭적 아님)
-- 반대칭적? m₀₁ = 1이고 m₁₀ = 0 ✓, m₂₁ = 1이고 m₁₂ = 0 ✓ → /- 여기를 채우세요 -/
-- 전이적? (1,2) ∈ R이고 (2,2) ∈ R이면 (1,2) ∈ R? → /- 여기를 채우세요 -/
```

<details>
<summary>💡 답 보기</summary>

- 반대칭적? ✓ (대각선 밖에서 1이 마주보지 않음)
- 전이적? ✓ (R의 모든 경로가 다시 R로 돌아옴)
  - (1,2)∈R, (2,2)∈R → (1,2)∈R ✓
  - (2,2)∈R, (2,2)∈R → (2,2)∈R ✓
  - (3,2)∈R, (2,2)∈R → (3,2)∈R ✓
</details>

---

## 7. 연습 문제 — 레벨 2: skeleton 채우기

### 연습 7.1: 부울 곱 직접 계산 (Rosen 연습문제 15a)

R을 다음 행렬로 표현되는 관계라 하자. R²을 표현하는 행렬을 구하라.

```
M_R = [0 1 0]
      [0 0 1]
      [1 1 0]
```

```lean
def M_7_1 : Fin 3 → Fin 3 → ℕ
  | 0, 0 => 0  | 0, 1 => 1  | 0, 2 => 0
  | 1, 0 => 0  | 1, 1 => 0  | 1, 2 => 1
  | 2, 0 => 1  | 2, 1 => 1  | 2, 2 => 0

-- R² = M_R ⊙ M_R의 각 성분을 계산하라
-- (0,0): (0∧0)∨(1∧0)∨(0∧1) = ?
-- (0,1): (0∧1)∨(1∧0)∨(0∧1) = ?
-- ... (나머지도 계산)

-- 계산기 검증:
#eval showMatrix (boolPow M_7_1 2)
-- 답: sorry  -- 직접 계산한 결과와 비교하라!
```

<details>
<summary>💡 답 보기</summary>

```
R²의 행렬:
[0 0 1]    -- (0,0): 0, (0,1): 0, (0,2): 1∧1=1
[1 1 0]    -- (1,0): 0∨0∨1=1, (1,1): 0∨0∨1=1, (1,2): 0
[0 1 1]    -- (2,0): 0, (2,1): 0∨0∨0=0→wait...
```

실행으로 확인:
`#eval showMatrix (boolPow M_7_1 2)` → `[[0, 0, 1], [1, 1, 0], [0, 1, 1]]`
</details>

### 연습 7.2: 반사적 행렬 증명 (Lean 4)

```lean
-- 다음 행렬이 반사적 관계를 나타내는지 증명하라
def M_7_2 : Fin 3 → Fin 3 → ℕ
  | 0, 0 => 1  | 0, 1 => 0  | 0, 2 => 1
  | 1, 0 => 1  | 1, 1 => 1  | 1, 2 => 0
  | 2, 0 => 0  | 2, 1 => 1  | 2, 2 => 1

example : isReflexiveMatrix M_7_2 := by
  sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
example : isReflexiveMatrix M_7_2 := by
  intro i
  fin_cases i <;> rfl
```
</details>

### 연습 7.3: 대칭적이 아님을 증명 (Lean 4)

```lean
-- M_7_2가 대칭적이지 않음을 증명하라
example : ¬ isSymmetricMatrix M_7_2 := by
  sorry
```

<details>
<summary>💡 힌트</summary>

반례를 찾아라. M_7_2 0 1 = 0이지만 M_7_2 1 0 = 1이다. `intro h`로 가정한 후 `have := h 0 1`로 모순을 도출한다.
</details>

<details>
<summary>💡 답 보기</summary>

```lean
example : ¬ isSymmetricMatrix M_7_2 := by
  intro h
  have := h 0 1
  simp [M_7_2] at this
```
</details>

---

## 8. 연습 문제 — 레벨 3: sorry 채우기 (독립 증명)

### 연습 8.1: 합집합 행렬의 성질

두 반사적 관계의 합집합도 반사적임을 증명하라.

```lean
theorem union_reflexive
    (h₁ : isReflexiveMatrix M₁) (h₂ : isReflexiveMatrix M₂) :
    isReflexiveMatrix (matOr M₁ M₂) := by
  sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
theorem union_reflexive
    (h₁ : isReflexiveMatrix M₁) (h₂ : isReflexiveMatrix M₂) :
    isReflexiveMatrix (matOr M₁ M₂) := by
  intro i
  simp [matOr, h₁ i, h₂ i]
```
</details>

### 연습 8.2: 교집합 행렬의 대칭성

두 대칭적 관계의 교집합도 대칭적임을 증명하라.

```lean
theorem inter_symmetric
    (h₁ : isSymmetricMatrix M₁) (h₂ : isSymmetricMatrix M₂) :
    isSymmetricMatrix (matAnd M₁ M₂) := by
  sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
theorem inter_symmetric
    (h₁ : isSymmetricMatrix M₁) (h₂ : isSymmetricMatrix M₂) :
    isSymmetricMatrix (matAnd M₁ M₂) := by
  intro i j
  simp [matAnd, h₁ i j, h₂ i j]
```
</details>

### 연습 8.3: 대칭 행렬의 전치 (도전!)

관계가 대칭적이면 M\_R = (M\_R)ᵀ 임을 증명하라. (전치 행렬 정의 포함)

```lean
-- 전치 행렬 정의
def transpose (M : Fin n → Fin n → ℕ) : Fin n → Fin n → ℕ :=
  fun i j => M j i

-- 대칭적 ↔ M = Mᵀ
theorem symmetric_iff_transpose (M : Fin n → Fin n → ℕ) :
    isSymmetricMatrix M ↔ (∀ i j, M i j = transpose M i j) := by
  sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
theorem symmetric_iff_transpose (M : Fin n → Fin n → ℕ) :
    isSymmetricMatrix M ↔ (∀ i j, M i j = transpose M i j) := by
  constructor
  · intro h i j
    simp [transpose, h i j]
  · intro h i j
    have := h i j
    simp [transpose] at this
    exact this
```
</details>

---

## 9. 사용된 Lean 4 전술 · 함수 정리

| 전술/함수 | 용도 | 예시 |
|---------|------|------|
| `Fin n` | 0부터 n-1까지의 유한 타입 | `Fin 3` = {0, 1, 2} |
| `fin_cases i` | Fin n의 모든 경우 분기 | 행렬 성분 검사에 사용 |
| `<;>` | 모든 하위 목표에 전술 적용 | `fin_cases i <;> rfl` |
| `List.finRange n` | [0, 1, ..., n-1] 리스트 | 행렬 출력에 사용 |
| `List.any` | 하나라도 참이면 true | 부울 곱에서 OR |
| `List.contains` | 원소 소속 검사 | 인접 행렬 생성 |
| `max`, `min` | 최대/최소 | 합집합/교집합 행렬 |
| `showMatrix` | 행렬을 리스트로 출력 | `#eval showMatrix M` |

---

## 10. 핵심 요약

1. 유한집합 사이의 관계는 **0-1 행렬**로 표현할 수 있다: m_{ij} = 1이면 (aᵢ, bⱼ) ∈ R.
2. 행렬의 패턴으로 관계의 성질을 판단한다:
   - **반사적**: 대각선 모두 1
   - **대칭적**: M = Mᵀ (대칭 행렬)
   - **반대칭적**: 대각선 밖에서 1이 마주보지 않음
3. 관계의 **합집합** = 행렬의 원소별 OR, **교집합** = 원소별 AND.
4. 관계의 **합성** S ∘ R은 행렬의 **부울 곱** M\_R ⊙ M\_S로 계산한다.
5. **방향성 그래프**는 관계의 시각적 표현: 꼭지점 = 원소, 화살표 = 순서쌍.
6. Lean 4에서 `Fin n → Fin n → ℕ`로 행렬을, `List (Fin n × Fin n)`으로 그래프를 표현한다.
7. `fin_cases` 전술은 유한 타입의 모든 경우를 나열하는 강력한 도구이다.

---

> **다음 파트 예고**: Part 12-E에서는 **관계의 폐쇄** (Section 9.4)를 다룬다. 반사적 폐쇄, 대칭적 폐쇄, **전이 폐쇄**(transitive closure)의 개념과 **워셜 알고리즘**(Warshall's Algorithm)을 배우고, Lean 4로 구현한다!
