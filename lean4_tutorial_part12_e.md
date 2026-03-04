# Lean4 완전 정복 가이드 —  Part 12-E: 관계의 폐쇄 (Closure of Relations)

> **Rosen 이산수학 8판 · Section 9.4 기반**
> 『Mathematics in Lean』 + Lean 4 공식화

---

## 0. 들어가며: 이 파트에서 배울 것

지금까지 관계의 성질(반사적, 대칭적, 반대칭적, 전이적)을 배웠다. 그런데 주어진 관계가 원하는 성질을 갖지 않을 때는 어떻게 할까? 이때 사용하는 것이 바로 **폐쇄**(closure)이다.

폐쇄란 "원래 관계를 포함하면서 원하는 성질을 만족시키는 **가장 작은** 관계"이다. 마치 울타리를 치듯이, 원래 관계를 감싸서 빈 곳을 메꾸는 것이다.

이 파트에서 다루는 내용:

1. **폐쇄의 일반적 정의** — 성질 P에 대한 폐쇄
2. **반사 폐쇄**(reflexive closure) — R ∪ Δ
3. **대칭 폐쇄**(symmetric closure) — R ∪ R⁻¹
4. **전이 폐쇄**(transitive closure) — 가장 복잡하고 중요한 폐쇄
5. **경로와 연결 관계** — 방향성 그래프에서의 경로
6. **워셜 알고리즘**(Warshall's Algorithm) — 전이 폐쇄의 효율적 계산

### 이 파트에서 사용하는 핵심 Lean 4 개념

| 개념 | 설명 |
|------|------|
| `Relation.ReflTransGen` | 반사-전이 폐쇄 (Mathlib) |
| `Relation.TransGen` | 전이 폐쇄 (Mathlib) |
| `inductive` | 귀납적 타입 정의 |
| `Fin n` | {0, 1, ..., n-1} 유한 타입 |
| `decide` | 결정 가능한 명제 자동 판정 |
| `constructor` | ∧, ↔ 등의 분리 |
| `Or.inl`, `Or.inr` | ∨의 좌/우 증명 |

---

## 1. 폐쇄의 일반적 정의

### 1.1 직관적 이해

**비유**: 집합 A 위의 관계 R이 있는데, 이 관계가 어떤 성질 P를 만족시키지 않는다고 하자. "R을 최소한으로 확장해서 P를 만족시키게 만들자!" — 이것이 바로 **폐쇄**(closure)이다.

예를 들어, 친구 관계를 생각해 보자. "나 → 철수"라는 일방적 관계가 있다고 하자. 이것을 **대칭적**으로 만들려면 "철수 → 나"도 추가하면 된다. 이렇게 최소한의 추가만으로 원하는 성질을 만족시키는 것이 폐쇄이다.

### 1.2 형식적 정의

> **정의 1** (Rosen): R이 집합 A에 대한 관계이고, P에 대한 R의 **폐쇄**(closure)는, 만약 존재한다면, R을 포함하면서 성질 P를 만족시키는 집합 A에 대한 관계 S로, S는 R을 포함하고 성질 P를 갖는 모든 부분집합 A × A의 부분집합이다.

쉽게 풀어 말하면:
- R의 P-폐쇄 S는 **세 가지 조건**을 동시에 만족한다:
  1. R ⊆ S (원래 관계를 포함한다)
  2. S는 성질 P를 만족한다
  3. S는 위 두 조건을 만족하는 관계 중 **가장 작다**

### 1.3 Lean 4에서의 표현

Lean 4에서 관계는 `α → α → Prop` 타입으로 표현된다. 폐쇄의 일반적 개념을 정의해 보자:

```lean
-- 관계의 기본 타입
-- R : α → α → Prop 은 "α 위의 이항 관계"를 뜻한다
-- R a b 가 True이면 (a, b) ∈ R이라는 뜻이다

-- 폐쇄의 일반적 개념: R을 포함하고 성질 P를 만족하는 가장 작은 관계
-- (실제로 Lean에서는 각 폐쇄를 직접 귀납적으로 정의하는 것이 더 일반적이다)
def isClosure (R S : α → α → Prop) (P : (α → α → Prop) → Prop) : Prop :=
  (∀ a b, R a b → S a b) ∧  -- R ⊆ S
  P S ∧                       -- S는 성질 P를 만족
  (∀ T, (∀ a b, R a b → T a b) → P T → ∀ a b, S a b → T a b)
  -- S는 가장 작다: R을 포함하고 P를 만족하는 모든 T에 대해 S ⊆ T
```

위 정의가 복잡해 보이지만, 핵심은 간단하다. "원래 관계를 포함하고, 원하는 성질을 만족하며, 가능한 한 작다."

---

## 2. 반사 폐쇄 (Reflexive Closure)

### 2.1 정의와 직관

> **반사 폐쇄**(reflexive closure)란 관계 R을 포함하면서 **반사적**인 가장 작은 관계이다.

반사적이려면 모든 원소 a에 대해 (a, a)가 관계에 있어야 한다. 따라서 R에 빠져 있는 (a, a) 쌍들만 추가하면 된다!

수학적으로: **R의 반사 폐쇄 = R ∪ Δ**

여기서 Δ = {(a, a) | a ∈ A}는 A의 **대각 관계**(diagonal relation)이다.

### 2.2 예제 (Rosen 예제 1)

집합 A = {1, 2, 3}에 관한 관계 R = {(1, 1), (1, 2), (2, 1), (3, 2)}를 생각하자.

R은 **반사적이지 않다**. 왜냐하면 (2, 2)와 (3, 3)이 R에 포함되지 않기 때문이다.

R의 반사 폐쇄 = R ∪ {(1, 1), (2, 2), (3, 3)} = {(1, 1), (1, 2), (2, 1), (2, 2), (3, 2), (3, 3)}

이미 (1, 1) ∈ R이었으므로, 실질적으로 (2, 2)와 (3, 3)만 추가하면 된다.

### 2.3 정수 집합에 대한 예제

정수의 집합에 대한 관계 R = {(a, b) | a < b}의 반사 폐쇄는 무엇인가?

R ∪ Δ = {(a, b) | a < b} ∪ {(a, a) | a ∈ ℤ} = {(a, b) | a ≤ b}

"진짜 작다(strict less-than)"를 반사 폐쇄하면 "작거나 같다(less-than-or-equal)"가 된다! 이것은 매우 자연스러운 결과이다.

### 2.4 Lean 4 구현

```lean
-- 반사 폐쇄: 원래 관계이거나 같은 원소
def reflClosure (R : α → α → Prop) (a b : α) : Prop :=
  R a b ∨ a = b

-- 반사 폐쇄가 실제로 반사적임을 증명
theorem reflClosure_refl (R : α → α → Prop) (a : α) :
    reflClosure R a a := by
  -- reflClosure R a a = R a a ∨ a = a
  right   -- a = a를 증명하면 된다
  rfl     -- 같은 값이므로 자동

-- 반사 폐쇄가 원래 관계를 포함함을 증명
theorem subset_reflClosure (R : α → α → Prop) (a b : α) (h : R a b) :
    reflClosure R a b := by
  left    -- R a b를 증명하면 된다
  exact h -- 가정 h가 바로 이것
```

### 2.5 유한 집합에서의 구체적 예

```lean
-- Fin 3 = {0, 1, 2} 위의 관계 정의
def R_ex1 : Fin 3 → Fin 3 → Prop
  | 0, 0 => True   -- (1,1) in textbook
  | 0, 1 => True   -- (1,2)
  | 1, 0 => True   -- (2,1)
  | 2, 1 => True   -- (3,2)
  | _, _ => False

-- R_ex1은 반사적이지 않다: (1,1)=True지만 (2,2)=False
example : ¬(R_ex1 1 1) := by
  simp [R_ex1]

-- 반사 폐쇄 후에는 (1,1)도 성립한다
example : reflClosure R_ex1 1 1 := by
  right; rfl    -- 1 = 1 이므로

-- 반사 폐쇄 후에는 (2,2)도 성립한다
example : reflClosure R_ex1 2 2 := by
  right; rfl    -- 2 = 2 이므로
```

---

## 3. 대칭 폐쇄 (Symmetric Closure)

### 3.1 정의와 직관

> **대칭 폐쇄**(symmetric closure)란 관계 R을 포함하면서 **대칭적**인 가장 작은 관계이다.

대칭적이려면 (a, b) ∈ R일 때마다 (b, a)도 관계에 있어야 한다. 따라서 R에 있는 모든 (a, b)에 대해 (b, a)를 추가하면 된다!

수학적으로: **R의 대칭 폐쇄 = R ∪ R⁻¹**

여기서 R⁻¹ = {(b, a) | (a, b) ∈ R}은 R의 **역관계**(inverse relation)이다.

### 3.2 예제 (Rosen 예제 2)

양의 정수의 집합에 대한 관계 R = {(a, b) | a > b}의 대칭 폐쇄는 무엇인가?

R ∪ R⁻¹ = {(a, b) | a > b} ∪ {(b, a) | a > b}
       = {(a, b) | a > b} ∪ {(a, b) | a < b}
       = {(a, b) | a ≠ b}

R은 "첫 번째 원소가 두 번째 원소보다 큰" 모든 순서쌍을 포함하고, R⁻¹은 "첫 번째 원소가 두 번째 원소보다 작은" 모든 순서쌍을 포함한다. 합하면 "두 원소가 다른" 모든 순서쌍이 된다!

### 3.3 Lean 4 구현

```lean
-- 대칭 폐쇄: 원래 관계이거나 역방향
def symmClosure (R : α → α → Prop) (a b : α) : Prop :=
  R a b ∨ R b a

-- 대칭 폐쇄가 실제로 대칭적임을 증명
theorem symmClosure_symm (R : α → α → Prop) (a b : α)
    (h : symmClosure R a b) : symmClosure R b a := by
  -- h : R a b ∨ R b a
  -- 목표 : R b a ∨ R a b
  rcases h with hab | hba
  · right; exact hab    -- R a b → 오른쪽으로 R a b
  · left; exact hba     -- R b a → 왼쪽으로 R b a

-- 대칭 폐쇄가 원래 관계를 포함함을 증명
theorem subset_symmClosure (R : α → α → Prop) (a b : α) (h : R a b) :
    symmClosure R a b := by
  left; exact h
```

### 3.4 반사 폐쇄와 대칭 폐쇄의 행렬 표현 (Part 12-D 복습)

0-1 행렬로 표현할 때:
- **반사 폐쇄**: M_R의 대각선을 모두 1로 만든다 → M_R ∨ I_n
- **대칭 폐쇄**: M_R과 그 전치 행렬의 합집합 → M_R ∨ M_R^T

이것은 Part 12-D에서 배운 행렬 연산과 직접 대응된다!

---

## 4. 전이 폐쇄 (Transitive Closure) — 핵심 주제

### 4.1 왜 전이 폐쇄가 중요한가?

반사 폐쇄와 대칭 폐쇄는 간단하다. 각각 대각 원소를 추가하거나 역방향을 추가하면 끝이다. 그런데 **전이 폐쇄**(transitive closure)는 훨씬 복잡하다!

왜 복잡한가? 전이성을 만족시키려면 (a, b)와 (b, c)가 있을 때 (a, c)를 추가해야 하는데, 새로 추가된 (a, c)가 다른 쌍과 결합하여 또 다른 쌍을 만들어낼 수 있기 때문이다. 이 과정이 연쇄적으로 일어날 수 있다!

**예시**: 집합 {1, 2, 3, 4}에 대한 관계 R = {(1, 3), (1, 4), (2, 1), (3, 2)}를 생각하자.

R은 전이적이지 않다. (2, 1)과 (1, 3)이 R에 포함되어 있으므로 전이적이려면 (2, 3)이 필요하지만, (2, 3) ∉ R이다.

단순히 빠진 쌍을 추가하면 될까? (2, 3)을 추가하면 또 새로운 전이성 위반이 생긴다:
- (2, 3)과 (3, 2) → (2, 2) 필요!
- (1, 3)과 (3, 2) → (1, 2) 필요!
- ... 이 과정이 계속된다.

결국 R에 없는 쌍 (1, 2), (2, 3), (2, 4), (3, 1), (3, 3), (3, 4)를 모두 추가해야 한다. 복잡하다!

### 4.2 경로(Path)를 이용한 이해

전이 폐쇄를 이해하는 가장 좋은 방법은 **방향성 그래프의 경로**를 이용하는 것이다.

> **정의 2** (Rosen): 방향성 그래프 G의 a에서 b로의 **경로**(path)는 G에 있는 모서리의 서열 (x₀, x₁), (x₁, x₂), ..., (x_{n-1}, x_n)이다. n은 음이 아닌 정수이고, x₀ = a이고 x_n = b이다. 경로의 **길이**(length)는 n이다.

즉, 경로란 화살표를 따라 a에서 b까지 이동하는 것이다. 길이 1 이상이고 시작점과 끝점이 같은 경로를 **순환**(circuit 또는 cycle)이라 한다.

### 4.3 R^n과 경로의 관계

> **정리 1** (Rosen): R을 집합 A에 대한 관계라 하자. n이 양의 정수일 때 a에서 b로 가는 길이 n의 경로가 있다는 것과 (a, b) ∈ R^n은 **동치**이다.

여기서 R^n은 R을 n번 **합성**(composition)한 것이다:
- R¹ = R
- R² = R ∘ R (R을 두 번 합성)
- R^n = R ∘ R^{n-1}

**직관**: (a, b) ∈ R²이라는 것은 "a에서 어떤 중간점 c를 거쳐 b에 도달할 수 있다"는 뜻이다. (a, b) ∈ R^n이라는 것은 "정확히 n번의 이동으로 a에서 b에 도달할 수 있다"는 뜻이다.

```lean
-- R의 n번 합성을 정의
def relPow (R : α → α → Prop) : ℕ → α → α → Prop
  | 0     => fun a b => a = b        -- R⁰ = 항등 관계
  | n + 1 => fun a b => ∃ c, R a c ∧ relPow R n c b  -- Rⁿ⁺¹ = R ∘ Rⁿ

-- R¹ = R 임을 증명
theorem relPow_one (R : α → α → Prop) (a b : α) :
    relPow R 1 a b ↔ R a b := by
  constructor
  · rintro ⟨c, hac, hcb⟩
    -- hcb : relPow R 0 c b = (c = b)
    simp [relPow] at hcb
    rw [hcb] at hac
    exact hac
  · intro hab
    exact ⟨b, hab, rfl⟩

-- R² 의미: 중간점을 거쳐 도달 가능
example (R : α → α → Prop) (a b : α) :
    relPow R 2 a b ↔ ∃ c, R a c ∧ R c b := by
  constructor
  · rintro ⟨c, hac, d, hcd, hdb⟩
    simp [relPow] at hdb
    rw [hdb] at hcd
    exact ⟨c, hac, hcd⟩
  · rintro ⟨c, hac, hcb⟩
    exact ⟨c, hac, b, hcb, rfl⟩
```

### 4.4 연결 관계와 전이 폐쇄

> **정의 3** (Rosen): R을 집합 A에 관한 관계라 하자. **연결 관계**(connectivity relation) R*는 R에 a에서 b로 가는 길이 1 이상의 경로가 있는 쌍 (a, b)로 구성된다.

수학적으로: **R* = R ∪ R² ∪ R³ ∪ ...**

> **정리 2** (Rosen): 관계 R의 **전이 폐쇄**는 연결 관계 R*와 **동일**하다.

이것이 핵심이다! 전이 폐쇄 = "어떤 길이의 경로든 존재하면 연결"

### 4.5 Lean 4에서의 전이 폐쇄

Lean 4의 Mathlib에는 `Relation.TransGen`이라는 전이 폐쇄가 이미 정의되어 있다. 하지만 먼저 직접 정의해 보자:

```lean
-- 전이 폐쇄의 귀납적 정의
-- "R로 한 번 이동하거나, R로 한 번 이동 후 전이 폐쇄로 더 이동"
inductive TransClosure (R : α → α → Prop) : α → α → Prop where
  | single : R a b → TransClosure R a b
  | step   : R a c → TransClosure R c b → TransClosure R a b

-- 전이 폐쇄가 원래 관계를 포함함
theorem TransClosure_of_R (R : α → α → Prop) (a b : α) (h : R a b) :
    TransClosure R a b :=
  TransClosure.single h

-- 전이 폐쇄가 전이적임
theorem TransClosure_trans (R : α → α → Prop) (a b c : α)
    (hab : TransClosure R a b) (hbc : TransClosure R b c) :
    TransClosure R a c := by
  induction hab with
  | single hr => exact TransClosure.step hr hbc
  | step hr _ ih => exact TransClosure.step hr (ih hbc)
```

**코드 해설**:

1. `inductive TransClosure`는 **귀납적 타입**(inductive type)을 정의한다. 이것은 "가장 작은 관계"를 직접 정의하는 Lean 4의 강력한 도구이다.

2. 두 가지 **생성자**(constructor)가 있다:
   - `single`: R에서 직접 한 번 이동 (길이 1의 경로)
   - `step`: R에서 한 번 이동 후 전이 폐쇄를 통해 더 이동 (길이 2 이상의 경로)

3. 전이성 증명에서 `induction hab`은 "hab이 어떤 생성자로 만들어졌는지"에 따라 경우를 나눈다.

---

## 5. 유한 집합에서의 전이 폐쇄

### 5.1 보조정리 1

> **보조정리 1** (Rosen): A가 n개의 원소를 갖는 집합이고, R을 A에 대한 관계라고 하자. R에 a에서 b로 가는 길이 1 이상의 경로가 있다면, 길이 n을 초과하지 않는 경로가 있다. 또, a ≠ b일 때 a에서 b로 가는 길이 1 이상의 경로가 있다면, 길이 n - 1을 초과하지 않는 경로가 있다.

**직관**: 집합에 n개의 원소밖에 없으므로, n보다 긴 경로는 반드시 어떤 꼭지점을 두 번 이상 방문한다. 비둘기집 원리! 순환 부분을 잘라내면 더 짧은 경로를 얻을 수 있다.

이 보조정리 덕분에 유한 집합에서는 무한히 긴 경로를 검사할 필요가 없다:

> **R* = R ∪ R² ∪ R³ ∪ ... ∪ Rⁿ** (유한 합집합으로 충분!)

### 5.2 행렬을 이용한 전이 폐쇄 계산

> **정리 3** (Rosen): M_R이 n개의 원소를 갖는 집합에 대한 관계 R의 0-1 행렬이라고 하자. 그러면 전이 폐쇄 R*의 0-1 행렬은 다음과 같다.
>
> **M_{R*} = M_R ∨ M_R^{[2]} ∨ M_R^{[3]} ∨ ... ∨ M_R^{[n]}**

여기서 M_R^{[k]}는 M_R의 k번째 **부울 거듭제곱**(Boolean power)이고, ∨는 원소별 OR이다.

```lean
-- 유한 집합 {0, 1, 2}에서의 전이 폐쇄 예 (Rosen 예제 7)
-- M_R = [[1,0,1],[0,1,0],[1,1,0]]

def MR : Fin 3 → Fin 3 → Bool
  | 0, 0 => true  | 0, 1 => false | 0, 2 => true
  | 1, 0 => false | 1, 1 => true  | 1, 2 => false
  | 2, 0 => true  | 2, 1 => true  | 2, 2 => false

-- 부울 행렬 곱
def boolMatMul (A B : Fin 3 → Fin 3 → Bool) : Fin 3 → Fin 3 → Bool :=
  fun i j => (A i 0 && B 0 j) || (A i 1 && B 1 j) || (A i 2 && B 2 j)

-- 부울 행렬 합 (원소별 OR)
def boolMatOr (A B : Fin 3 → Fin 3 → Bool) : Fin 3 → Fin 3 → Bool :=
  fun i j => A i j || B i j

-- M_R² 계산
def MR2 : Fin 3 → Fin 3 → Bool := boolMatMul MR MR

-- M_R³ 계산
def MR3 : Fin 3 → Fin 3 → Bool := boolMatMul MR2 MR

-- 전이 폐쇄 = M_R ∨ M_R² ∨ M_R³
def MRstar : Fin 3 → Fin 3 → Bool :=
  boolMatOr (boolMatOr MR MR2) MR3

-- 결과 확인: 모든 위치가 1 (자기 자신 제외한 일부)
#eval MRstar 0 0  -- true
#eval MRstar 0 1  -- true
#eval MRstar 0 2  -- true
#eval MRstar 1 0  -- false (1에서 0으로 가는 경로 없음? 확인 필요)
```

---

## 6. 워셜 알고리즘 (Warshall's Algorithm)

### 6.1 동기

정리 3의 방법으로 전이 폐쇄를 구하려면 O(n⁴) 비트 연산이 필요하다(n개의 행렬 곱 + 결합). 1960년 스티븐 **워셜**(Stephen Warshall)이 고안한 **워셜 알고리즘**은 더 효율적인 O(n³) 방법이다!

### 6.2 내부 꼭지점의 개념

워셜 알고리즘의 핵심 아이디어는 **내부 꼭지점**(interior vertices)이다.

경로 a, x₁, x₂, ..., x_{m-1}, b에서 **내부 꼭지점**은 x₁, x₂, ..., x_{m-1}이다. 즉, 처음 꼭지점(a)과 마지막 꼭지점(b)을 **제외한** 나머지 꼭지점들이다.

### 6.3 알고리즘 아이디어

행렬 W_k를 "내부 꼭지점이 집합 {v₁, v₂, ..., v_k}에서 온 경로"가 존재하는지를 나타내는 0-1 행렬이라 하자.

- W₀ = M_R (내부 꼭지점 없음 → 직접 연결만)
- W_n = M_{R*} (모든 꼭지점을 내부 꼭지점으로 허용 → 전이 폐쇄)

**핵심 관찰** (보조정리 2):

> w_{ij}^{[k]} = w_{ij}^{[k-1]} ∨ (w_{ik}^{[k-1]} ∧ w_{kj}^{[k-1]})

이것이 의미하는 바:
- v_i에서 v_j로의 경로가 {v₁, ..., v_k}를 내부 꼭지점으로 사용할 수 있다면,
  두 가지 경우 중 하나이다:
  1. v_k를 거치지 않는 경로가 있다 (→ w_{ij}^{[k-1]} = 1)
  2. v_i에서 v_k를 거쳐 v_j로 가는 경로가 있다 (→ w_{ik}^{[k-1]} = 1 **그리고** w_{kj}^{[k-1]} = 1)

### 6.4 Lean 4 구현

```lean
-- 워셜 알고리즘 구현
-- n: 꼭지점 수, adj: 인접 행렬
def warshall (n : ℕ) (adj : Fin n → Fin n → Bool) : Fin n → Fin n → Bool :=
  loop n adj
where
  loop : ℕ → (Fin n → Fin n → Bool) → (Fin n → Fin n → Bool)
  | 0, w     => w
  | k + 1, w =>
    let k' : Fin n := ⟨k, by omega⟩  -- k를 Fin n으로 변환 (k < n 보장 필요)
    loop k (fun i j => w i j || (w i k' && w k' j))
```

위 코드는 간소화된 버전이다. 실제로는 k < n 조건이 필요하므로, 좀 더 정교한 구현이 필요하다. 아래는 더 명확한 버전이다:

```lean
-- 더 명확한 워셜 알고리즘 (리스트 기반)
def warshallStep (w : Fin n → Fin n → Bool) (k : Fin n) :
    Fin n → Fin n → Bool :=
  fun i j => w i j || (w i k && w k j)

def warshallAux : (k : ℕ) → (Fin n → Fin n → Bool) → (Fin n → Fin n → Bool)
  | 0, w     => w
  | k + 1, w => warshallAux k (warshallStep w ⟨k, by omega⟩)
```

### 6.5 예제 (Rosen 예제 8)

그래프: a → d, a → c, b → a, c → b (4개의 꼭지점 a, b, c, d)

v₁ = a, v₂ = b, v₃ = c, v₄ = d로 번호를 매기자.

```
W₀ = [[0,0,0,1],    -- a에서 직접: d만
      [1,0,1,0],     -- b에서 직접: a, c
      [1,0,0,1],     -- c에서 직접: a, d
      [0,0,1,0]]     -- d에서 직접: c
```

W₁ (a를 내부 꼭지점으로 허용):
- b에서 d로의 새 경로: b→a→d ✓
- c에서 d로의 새 경로: 이미 있음

```
W₁ = [[0,0,0,1],
      [1,0,1,1],     -- (b,d) 추가!
      [1,0,0,1],
      [0,0,1,0]]
```

이 과정을 W₂, W₃, W₄까지 반복하면 전이 폐쇄를 얻는다.

---

## 7. 연습 문제 — 레벨 1: 괄호 채우기

### 연습 7.1: 반사 폐쇄 기본 (Rosen 연습문제 1a)

```lean
-- R = {(0, 1), (1, 1), (1, 2), (2, 0), (2, 2), (3, 0)}
-- 집합 {0, 1, 2, 3} 위의 관계
-- R의 반사 폐쇄를 구하라

-- 반사 폐쇄 = R ∪ {(0,0), (1,1), (2,2), (3,3)}
-- = R ∪ {(0,0), (3,3)}  (이미 (1,1), (2,2) ∈ R)

def R71 : Fin 4 → Fin 4 → Prop
  | 0, 1 => True | 1, 1 => True | 1, 2 => True
  | 2, 0 => True | 2, 2 => True | 3, 0 => True
  | _, _ => False

-- 반사 폐쇄에서 (0,0) 성립
example : reflClosure R71 0 0 := by
  {① right 또는 left 중 무엇?}
  {② 나머지를 증명하라}
```

<details>
<summary>💡 답 보기</summary>

```lean
example : reflClosure R71 0 0 := by
  right    -- ① a = b 쪽을 선택
  rfl      -- ② 0 = 0
```

**설명**: (0, 0)은 원래 R71에 없지만 (R71 0 0 = False), 반사 폐쇄의 정의 `R a b ∨ a = b`에서 오른쪽 `0 = 0`이 성립하므로 반사 폐쇄에는 포함된다!
</details>

### 연습 7.2: 대칭 폐쇄 기본

```lean
-- "a > b" 관계의 대칭 폐쇄가 "a ≠ b"임을 Nat에서 확인
-- 구체적 예: 5와 3에 대해

-- 대칭 폐쇄에서 (5, 3) 성립: 5 > 3
example : symmClosure (fun a b : ℕ => a > b) 5 3 := by
  {③ left 또는 right 중 무엇?}
  {④ 부등식을 증명하라 (omega 사용)}

-- 대칭 폐쇄에서 (3, 5) 성립: 역방향
example : symmClosure (fun a b : ℕ => a > b) 3 5 := by
  {⑤ left 또는 right 중 무엇?}
  {⑥ 부등식을 증명하라}
```

<details>
<summary>💡 답 보기</summary>

```lean
example : symmClosure (fun a b : ℕ => a > b) 5 3 := by
  left      -- ③ R a b 쪽 (5 > 3)
  omega     -- ④ 5 > 3 자동 증명

example : symmClosure (fun a b : ℕ => a > b) 3 5 := by
  right     -- ⑤ R b a 쪽 (5 > 3)
  omega     -- ⑥ 5 > 3 자동 증명
```

**설명**: (5, 3)은 5 > 3이므로 원래 관계에 속한다 (left). (3, 5)는 3 > 5가 아니므로 원래 관계에 없지만, 역방향 5 > 3이 성립하므로 대칭 폐쇄에 속한다 (right).
</details>

### 연습 7.3: 전이 폐쇄 기본

```lean
-- 관계 R: 1→2, 2→3 (Fin 4 위의 관계, 0-indexed로 0→1, 1→2)
def R73 : Fin 4 → Fin 4 → Prop
  | 0, 1 => True
  | 1, 2 => True
  | _, _ => False

-- 전이 폐쇄에서 (0, 2) 성립: 0→1→2 경로
example : TransClosure R73 0 2 := by
  apply TransClosure.step
  · {⑦ R73 0 1을 증명하라}
  · apply TransClosure.{⑧ single 또는 step?}
    {⑨ R73 1 2를 증명하라}
```

<details>
<summary>💡 답 보기</summary>

```lean
example : TransClosure R73 0 2 := by
  apply TransClosure.step
  · trivial    -- ⑦ R73 0 1 = True
  · apply TransClosure.single  -- ⑧ single (마지막 단계)
    trivial    -- ⑨ R73 1 2 = True
```

**설명**: `TransClosure.step`으로 "0에서 1로 한 번 이동 후 전이 폐쇄로 계속"을 적용하고, `TransClosure.single`로 "1에서 2로 직접 이동"을 적용한다. 결과: 0→1→2 경로!
</details>

---

## 8. 연습 문제 — 레벨 2: skeleton 채우기

### 연습 8.1: 반사 폐쇄가 가장 작은 반사적 관계임을 증명

```lean
-- 반사 폐쇄의 최소성: R ⊆ S이고 S가 반사적이면 reflClosure R ⊆ S
theorem reflClosure_minimal (R S : α → α → Prop)
    (hRS : ∀ a b, R a b → S a b)         -- R ⊆ S
    (hRefl : ∀ a, S a a)                   -- S는 반사적
    (a b : α) (h : reflClosure R a b) :
    S a b := by
  rcases h with hab | heq
  · -- hab : R a b인 경우
    sorry  -- hRS를 사용하라
  · -- heq : a = b인 경우
    sorry  -- heq로 치환 후 hRefl 사용
```

<details>
<summary>💡 답 보기</summary>

```lean
theorem reflClosure_minimal (R S : α → α → Prop)
    (hRS : ∀ a b, R a b → S a b)
    (hRefl : ∀ a, S a a)
    (a b : α) (h : reflClosure R a b) :
    S a b := by
  rcases h with hab | heq
  · exact hRS a b hab
  · rw [heq]; exact hRefl b
```

**설명**: 
- `R a b`인 경우: R ⊆ S이므로 S a b
- `a = b`인 경우: a를 b로 치환하면 S b b, 이것은 S의 반사성으로 성립
</details>

### 연습 8.2: 대칭 폐쇄가 가장 작은 대칭적 관계임을 증명

```lean
theorem symmClosure_minimal (R S : α → α → Prop)
    (hRS : ∀ a b, R a b → S a b)         -- R ⊆ S
    (hSymm : ∀ a b, S a b → S b a)        -- S는 대칭적
    (a b : α) (h : symmClosure R a b) :
    S a b := by
  rcases h with hab | hba
  · sorry  -- R a b → S a b
  · sorry  -- R b a → S b a → S a b
```

<details>
<summary>💡 답 보기</summary>

```lean
theorem symmClosure_minimal (R S : α → α → Prop)
    (hRS : ∀ a b, R a b → S a b)
    (hSymm : ∀ a b, S a b → S b a)
    (a b : α) (h : symmClosure R a b) :
    S a b := by
  rcases h with hab | hba
  · exact hRS a b hab
  · exact hSymm b a (hRS b a hba)
```

**설명**: 
- `R a b`인 경우: R ⊆ S이므로 직접 S a b
- `R b a`인 경우: R ⊆ S로 S b a를 얻고, S의 대칭성으로 S a b
</details>

### 연습 8.3: 전이 폐쇄가 원래 관계를 포함함

```lean
-- TransClosure는 R을 포함한다
-- 이미 증명했지만, 다시 해보자
theorem TransClosure_contains_R (R : α → α → Prop) (a b : α)
    (h : R a b) : TransClosure R a b := by
  sorry  -- TransClosure의 어떤 생성자를 사용하는가?
```

<details>
<summary>💡 답 보기</summary>

```lean
theorem TransClosure_contains_R (R : α → α → Prop) (a b : α)
    (h : R a b) : TransClosure R a b := by
  exact TransClosure.single h
```

**설명**: `TransClosure.single`은 R에서 직접 한 번 이동하는 경로(길이 1)를 만든다.
</details>

### 연습 8.4: 3단계 경로 만들기

```lean
-- 0→1, 1→2, 2→3 관계에서 0→3 경로를 전이 폐쇄로 구성
def chain3 : Fin 4 → Fin 4 → Prop
  | 0, 1 => True
  | 1, 2 => True
  | 2, 3 => True
  | _, _ => False

-- 0에서 3으로 가는 경로: 0→1→2→3
example : TransClosure chain3 0 3 := by
  sorry
  -- 힌트: TransClosure.step을 두 번, TransClosure.single을 한 번 사용
```

<details>
<summary>💡 답 보기</summary>

```lean
example : TransClosure chain3 0 3 := by
  apply TransClosure.step (trivial : chain3 0 1)
  apply TransClosure.step (trivial : chain3 1 2)
  exact TransClosure.single (trivial : chain3 2 3)
```

**설명**: 
1. `TransClosure.step`: 0에서 1로 이동 (chain3 0 1 = True), 나머지는 전이 폐쇄
2. `TransClosure.step`: 1에서 2로 이동 (chain3 1 2 = True), 나머지는 전이 폐쇄
3. `TransClosure.single`: 2에서 3으로 직접 이동 (chain3 2 3 = True)

결과: 0→1→2→3, 길이 3의 경로!
</details>

---

## 9. 연습 문제 — 레벨 3: sorry 채우기 (독립 증명)

### 연습 9.1: 반사 폐쇄의 반사 폐쇄는 자기 자신 (멱등성)

```lean
-- reflClosure (reflClosure R) = reflClosure R
-- 즉, 이미 반사적인 관계를 다시 반사 폐쇄해도 바뀌지 않는다
theorem reflClosure_idempotent (R : α → α → Prop) (a b : α) :
    reflClosure (reflClosure R) a b ↔ reflClosure R a b := by
  sorry
```

<details>
<summary>💡 힌트</summary>

`constructor`로 양방향을 나누어 증명한다.
- (→): `reflClosure (reflClosure R) a b`를 분석하면 두 경우가 나온다.
- (←): `reflClosure R a b`이면 `reflClosure (reflClosure R) a b`임을 보인다.
</details>

<details>
<summary>💡 답 보기</summary>

```lean
theorem reflClosure_idempotent (R : α → α → Prop) (a b : α) :
    reflClosure (reflClosure R) a b ↔ reflClosure R a b := by
  constructor
  · intro h
    rcases h with h1 | heq
    · exact h1  -- reflClosure R a b 자체
    · rw [heq]; right; rfl  -- a = b이면 reflClosure R b b
  · intro h
    left; exact h  -- reflClosure R a b → reflClosure (reflClosure R) a b
```
</details>

### 연습 9.2: 대칭 폐쇄의 대칭 폐쇄는 자기 자신 (멱등성)

```lean
theorem symmClosure_idempotent (R : α → α → Prop) (a b : α) :
    symmClosure (symmClosure R) a b ↔ symmClosure R a b := by
  sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
theorem symmClosure_idempotent (R : α → α → Prop) (a b : α) :
    symmClosure (symmClosure R) a b ↔ symmClosure R a b := by
  constructor
  · intro h
    rcases h with h1 | h2
    · exact h1
    · -- h2 : symmClosure R b a
      exact symmClosure_symm R b a h2
  · intro h
    left; exact h
```
</details>

### 연습 9.3: 전이 폐쇄의 전이성 (독립 증명)

```lean
-- 전이 폐쇄의 핵심 성질: TransClosure R은 전이적이다
-- 이것을 다시 한 번 직접 증명해보라
theorem TransClosure_is_transitive (R : α → α → Prop) (a b c : α)
    (hab : TransClosure R a b) (hbc : TransClosure R b c) :
    TransClosure R a c := by
  sorry
```

<details>
<summary>💡 힌트</summary>

`hab`에 대해 `induction`을 사용한다. 두 가지 경우:
- `single hr`: R a b이고 hbc : TransClosure R b c → `step hr hbc`
- `step hr hab'` + 귀납 가설 `ih`: R a m, TransClosure R m b → `step hr (ih hbc)`
</details>

<details>
<summary>💡 답 보기</summary>

```lean
theorem TransClosure_is_transitive (R : α → α → Prop) (a b c : α)
    (hab : TransClosure R a b) (hbc : TransClosure R b c) :
    TransClosure R a c := by
  induction hab with
  | single hr => exact TransClosure.step hr hbc
  | step hr _ ih => exact TransClosure.step hr (ih hbc)
```

**설명**: 
- `single hr` 경우: a→b가 R의 한 단계이고, b→c가 전이 폐쇄. 따라서 a→b→...→c는 `step`으로 구성.
- `step hr hab'` 경우: a→m이 R의 한 단계, m→b가 전이 폐쇄, b→c가 전이 폐쇄. 귀납 가설로 m→c를 얻고, a→m→...→c는 `step`으로 구성.
</details>

### 연습 9.4: 반사 폐쇄와 대칭 폐쇄의 교환 (도전!)

```lean
-- 반사 폐쇄 후 대칭 폐쇄 = 대칭 폐쇄 후 반사 폐쇄?
-- 한 방향만 증명: reflClosure의 symmClosure ⊆ symmClosure의 reflClosure
theorem refl_symm_subset (R : α → α → Prop) (a b : α)
    (h : symmClosure (reflClosure R) a b) :
    reflClosure (symmClosure R) a b := by
  sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
theorem refl_symm_subset (R : α → α → Prop) (a b : α)
    (h : symmClosure (reflClosure R) a b) :
    reflClosure (symmClosure R) a b := by
  rcases h with h1 | h2
  · -- h1 : reflClosure R a b = R a b ∨ a = b
    rcases h1 with hr | heq
    · left; left; exact hr     -- R a b → symmClosure R a b
    · right; exact heq          -- a = b
  · -- h2 : reflClosure R b a = R b a ∨ b = a
    rcases h2 with hr | heq
    · left; right; exact hr    -- R b a → symmClosure R a b (역방향)
    · right; exact heq.symm     -- b = a → a = b
```
</details>

---

## 10. 워셜 알고리즘 구현 연습

### 연습 10.1: 워셜 한 단계 실행

```lean
-- 초기 행렬 (Rosen 예제 8의 W₀)
def W0 : Fin 4 → Fin 4 → Bool
  | 0, 0 => false | 0, 1 => false | 0, 2 => false | 0, 3 => true
  | 1, 0 => true  | 1, 1 => false | 1, 2 => true  | 1, 3 => false
  | 2, 0 => true  | 2, 1 => false | 2, 2 => false | 2, 3 => true
  | 3, 0 => false | 3, 1 => false | 3, 2 => true  | 3, 3 => false

-- W₁: v₁ = a (index 0)를 내부 꼭지점으로 허용
-- w_ij^[1] = w_ij^[0] ∨ (w_i0^[0] ∧ w_0j^[0])
def W1 : Fin 4 → Fin 4 → Bool := warshallStep W0 0

-- (1, 3) 확인: b에서 d로.
-- w_13^[1] = w_13^[0] ∨ (w_10^[0] ∧ w_03^[0])
--          = false   ∨ (true    ∧ true)
--          = true
-- b→a→d 경로 발견!
#eval W1 1 3  -- true를 확인하라
```

---

## 11. 핵심 요약

1. **폐쇄**(closure)란 관계 R을 포함하면서 원하는 성질을 만족시키는 **가장 작은** 관계이다.
2. **반사 폐쇄**(reflexive closure) = R ∪ Δ (대각 원소 추가). Lean 4: `R a b ∨ a = b`.
3. **대칭 폐쇄**(symmetric closure) = R ∪ R⁻¹ (역방향 추가). Lean 4: `R a b ∨ R b a`.
4. **전이 폐쇄**(transitive closure) = R* = R ∪ R² ∪ R³ ∪ ... (모든 경로). Lean 4: `inductive TransClosure`.
5. **경로**(path)란 방향성 그래프의 모서리를 따라 이동하는 서열이다. (a, b) ∈ Rⁿ은 길이 n의 경로 존재와 동치이다.
6. 유한 집합(n개 원소)에서 전이 폐쇄는 R ∪ R² ∪ ... ∪ Rⁿ으로 충분하다 (보조정리 1).
7. 행렬을 이용한 전이 폐쇄: M_{R*} = M_R ∨ M_R^{[2]} ∨ ... ∨ M_R^{[n]} (O(n⁴)).
8. **워셜 알고리즘**은 내부 꼭지점을 하나씩 추가하며 O(n³)으로 전이 폐쇄를 구한다.
9. Lean 4에서 `inductive`를 사용한 귀납적 정의는 폐쇄를 정의하는 자연스러운 방법이다.

---

## 12. 사용된 Lean 4 전술 정리

| 전술 | 용도 | 예시 |
|------|------|------|
| `left` / `right` | ∨의 좌/우 선택 | `left; exact h` |
| `rcases h with h1 \| h2` | ∨ 분해 | 경우 나누기 |
| `constructor` | ∧, ↔ 분리 | `constructor; intro h; ...` |
| `rfl` | 같은 값의 등식 | `a = a` |
| `rw [h]` | 등식을 이용한 치환 | `rw [heq]` |
| `exact` | 정확한 항으로 목표 완성 | `exact TransClosure.single h` |
| `trivial` | True 등 간단한 명제 | `(trivial : R 0 1)` |
| `induction ... with` | 귀납적 타입 분석 | 전이 폐쇄 증명 |
| `omega` | 산술 자동 증명 | 부등식, 크기 조건 |

---

> **다음 파트 예고**: Part 12-F에서는 **동치관계와 동치류** (Section 9.5)를 다룬다. 동치관계(반사적 + 대칭적 + 전이적)가 집합을 **분할**(partition)하는 방법, **동치류**(equivalence class)의 개념, 그리고 합동 클래스 모듈로 m을 배운다!
