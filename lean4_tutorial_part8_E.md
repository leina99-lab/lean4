# Lean4 Tutorial Part 8-E: **구조적 귀납법**(Structural Induction)과 **이진 트리**(Binary Trees)

> **기반 교재**: Kenneth H. Rosen, *Discrete Mathematics and Its Applications* 8판 5.3.4절, 5.3.5절  
> **참고 교재**: *Mathematics in Lean* Chapter 5.2, 5.4, Chapter 6.3  
> **선수 지식**: Part 8-A~8-D (수학적 귀납법, 강 귀납법, 재귀적 정의)

---

## 8E.0 이 파트에서 배우는 것

Part 8-D에서 **재귀적으로 정의된 함수와 집합**을 배웠다. 이번 파트에서는 재귀적으로 정의된 집합에 대한 결과를 증명하는 강력한 도구인 **구조적 귀납법**(structural induction)을 배운다.

이 파트에서 다루는 내용:

1. **구조적 귀납법**이란 무엇인가 — 재귀적 집합의 원소에 대한 귀납법
2. Lean4에서 `inductive` 타입 정의하기
3. **이진 트리**(binary tree)의 재귀적 정의
4. **포화 이진 트리**(full binary tree)의 꼭짓점 수 정리
5. **체계화 공식**(well-formed formulae)의 괄호 수 정리
6. **문자열 길이** 증명에서의 구조적 귀납법

> 💡 **핵심 아이디어**: 
>
> | 귀납 대상 | 귀납법 종류 | 예시 |
> |----------|-----------|------|
> | 자연수 | 수학적 귀납법 | $n = 0, 1, 2, \ldots$ |
> | 자연수 (여러 전제) | 강 귀납법 | 소인수 존재, 우표 문제 |
> | **재귀적 구조** | **구조적 귀납법** | 리스트, 트리, 수식 |

---

## 8E.1 구조적 귀납법이란 무엇인가?

### 직관: "작은 것에서 큰 것으로"

**구조적 귀납법**(structural induction)은 재귀적으로 정의된 집합의 원소가 어떤 성질을 갖는지 증명하는 방법이다. 그 구조는 다음과 같다:

| 단계 | 이름 | 하는 일 |
|------|------|--------|
| ① | **기본 단계** | 재귀적 정의의 **기본 단계**에서 명시된 원소들에 대해 성질이 성립함을 보인다 |
| ② | **귀납적 단계** | 재귀적 단계에서 **새로운 원소를 만드는 데 사용된 원소들**에 대해 성질이 참이면, 새로운 원소에 대해서도 성립함을 보인다 |

### 비유: 레고 블록

레고로 만든 구조물을 생각해 보자:

- **기본 단계** = 각각의 레고 블록은 "튼튼하다"
- **귀납적 단계** = 튼튼한 블록들을 올바르게 조립하면 결과물도 "튼튼하다"
- **결론** = 레고로 만든 **모든** 구조물은 "튼튼하다"

### 수학적 정의

$S$가 재귀적으로 정의된 집합이라 하자. $S$의 모든 원소에 대해 명제 $P$가 성립함을 보이려면:

1. **기본 단계**: $S$의 기본 원소 $s_1, s_2, \ldots$에 대해 $P(s_i)$가 참임을 보인다
2. **귀납적 단계**: $S$의 원소 $x_1, \ldots, x_k$에 대해 $P(x_1), \ldots, P(x_k)$가 참이라 가정하고, 재귀적 규칙으로 만들어진 새 원소 $y$에 대해 $P(y)$가 참임을 보인다

---

## 8E.2 Lean4의 `inductive` 타입: 구조적 귀납법의 기반

### 귀납적 타입이란?

Lean4에서 `inductive` 키워드로 정의된 타입은 자동으로 **구조적 귀납법 원리**를 갖는다. 이미 익숙한 예들이 있다:

```lean
-- 자연수: 가장 간단한 귀납적 타입
-- (실제 Lean4 라이브러리의 정의)
inductive Nat where
  | zero : Nat          -- 기본 단계: 0은 자연수
  | succ : Nat → Nat    -- 재귀적 단계: n이 자연수면 n+1도 자연수

-- 리스트: 또 다른 귀납적 타입
inductive List (α : Type) where
  | nil : List α                    -- 기본: 빈 리스트
  | cons : α → List α → List α     -- 재귀: 원소를 앞에 붙이기
```

`inductive`로 타입을 정의하면 Lean4가 자동으로 만들어 주는 것:

| 자동 생성 | 역할 | 예시 |
|---------|------|------|
| **생성자**(constructor) | 원소를 만드는 방법 | `Nat.zero`, `List.nil` |
| **재귀자**(recursor) | 귀납법/재귀 정의의 원리 | `Nat.rec`, `List.rec` |
| **매칭**(match) | 경우 나누기 | `match n with \| 0 => ... \| n+1 => ...` |

### Lean4에서 구조적 귀납법 사용하기

리스트에 대한 구조적 귀납법은 이미 Part 8-D에서 사용했다:

```lean
-- "빈 리스트"에서 시작하여 "원소를 추가"하는 각 단계에서 성립
theorem myLength_append (xs ys : List Nat) :
    myLength (xs ++ ys) = myLength xs + myLength ys := by
  induction xs with          -- xs에 대한 구조적 귀납법
  | nil =>                   -- 기본 단계: xs = []
    simp [myLength]
  | cons a as ih =>          -- 귀납적 단계: xs = a :: as
    simp [myLength]          -- ih: 더 작은 as에 대해 성립
    rw [ih]; omega
```

> 💡 **포인트**: Lean4의 `induction xs with`은 구조적 귀납법 그 자체이다!
> - `| nil =>` = 기본 단계 (빈 리스트)
> - `| cons a as ih =>` = 귀납적 단계 (원소 `a`를 추가, `ih`는 귀납 가정)

---

## 8E.3 이진 트리의 재귀적 정의 (Rosen 정의 3, 4, 5)

### 이진 트리란?

**이진 트리**(binary tree)는 컴퓨터 과학에서 가장 중요한 자료 구조 중 하나이다. 트리는 **꼭짓점**(vertex)들과 꼭짓점들의 쌍을 연결하는 **모서리**(edge)들로 구성된다.

일상에서 트리의 예:

- **가계도**: 조상-자손 관계
- **파일 시스템**: 폴더 안의 폴더
- **토너먼트 대진표**: 승자가 다음 라운드로

### 확장 이진 트리 (Rosen 정의 4)

**확장 이진 트리**(extended binary tree)는 다음과 같이 재귀적으로 정의된다:

| 단계 | 정의 |
|------|------|
| **기본 단계** | 공집합 ∅은 확장 이진 트리이다 |
| **재귀적 단계** | $T_1$과 $T_2$가 확장 이진 트리이면, 루트 $r$과 왼쪽 부분트리 $T_1$, 오른쪽 부분트리 $T_2$로 구성된 트리도 확장 이진 트리이다 |

Lean4로 정의하면:

```lean
-- 확장 이진 트리
inductive BinTree where
  | empty : BinTree                            -- 기본: 빈 트리
  | node : BinTree → BinTree → BinTree         -- 재귀: 왼쪽, 오른쪽 부분트리
  deriving Repr
```

이것을 그림으로 보면:

```
empty      node empty empty     node (node empty empty) empty
  ∅              •                       •
                / \                     / \
               ∅   ∅                   •   ∅
                                      / \
                                     ∅   ∅
```

### 포화 이진 트리 (Rosen 정의 5)

**포화 이진 트리**(full binary tree)는 모든 꼭짓점이 정확히 0개 또는 2개의 자식을 갖는 트리이다:

```lean
-- 포화 이진 트리
-- 차이: 빈 트리가 아니라 "잎"(leaf)이 기본 단계
inductive FullBinTree where
  | leaf : FullBinTree                                    -- 기본: 잎 (자식 없음)
  | node : FullBinTree → FullBinTree → FullBinTree        -- 재귀: 두 자식
  deriving Repr
```

그림:

```
leaf        node leaf leaf       node (node leaf leaf) leaf
  •              •                       •
                / \                     / \
               •   •                   •   •
                                      / \
                                     •   •
```

> 💡 **확장 이진 트리 vs 포화 이진 트리**
>
> | | 확장 이진 트리 | 포화 이진 트리 |
> |---|---|---|
> | 기본 | 빈 트리 (∅) | 잎 (•) |
> | 차이 | 빈 부분트리 허용 | 빈 부분트리 없음 |
> | 왼쪽/오른쪽 | 하나만 있을 수 있음 | 둘 다 있거나 둘 다 없음 |

---

## 8E.4 이진 트리에 대한 재귀 함수

### 높이와 꼭짓점 수 (Rosen 정의 6)

```lean
-- 포화 이진 트리의 높이
def FullBinTree.height : FullBinTree → Nat
  | .leaf => 0                    -- 잎의 높이 = 0
  | .node l r => 1 + max l.height r.height  -- 노드의 높이 = 1 + max(왼, 오)

-- 포화 이진 트리의 꼭짓점 수
def FullBinTree.numNodes : FullBinTree → Nat
  | .leaf => 1                    -- 잎 = 꼭짓점 1개
  | .node l r => 1 + l.numNodes + r.numNodes  -- 노드 자신 + 왼 + 오
```

### 연습: 구체적 계산 (괄호 채우기)

```lean
-- 잎 하나
def t0 : FullBinTree := .leaf
-- 잎 두 개를 가진 노드
def t1 : FullBinTree := .node .leaf .leaf
-- 더 큰 트리
def t2 : FullBinTree := .node (.node .leaf .leaf) .leaf

-- 높이 계산
example : t0.height = (______) := by rfl
example : t1.height = (______) := by rfl
example : t2.height = (______) := by rfl

-- 꼭짓점 수 계산
example : t0.numNodes = (______) := by rfl
example : t1.numNodes = (______) := by rfl
example : t2.numNodes = (______) := by rfl
```

<details>
<summary>💡 답 보기</summary>

```lean
example : t0.height = 0 := by rfl
example : t1.height = 1 := by rfl
example : t2.height = 2 := by rfl

example : t0.numNodes = 1 := by rfl
example : t1.numNodes = 3 := by rfl
example : t2.numNodes = 5 := by rfl
```

**계산 과정**:
- `t0` = leaf → 높이 0, 꼭짓점 1
- `t1` = node leaf leaf → 높이 1, 꼭짓점 3 (루트 + 잎 2개)
- `t2` = node (node leaf leaf) leaf → 높이 2, 꼭짓점 5 (루트 + 내부노드 + 잎 3개)

</details>

---

## 8E.5 핵심 정리: 포화 이진 트리의 꼭짓점 수 (Rosen 정리 2)

### 정리: $n(T) ≤ 2^{h(T)+1} - 1$

$T$가 포화 이진 트리이면, $n(T) ≤ 2^{h(T)+1} - 1$이다.

> 여기서 $n(T)$는 꼭짓점 수, $h(T)$는 높이이다.

### 증명: 구조적 귀납법

이 증명을 구조적 귀납법으로 수행한다:

**기본 단계**: $T = \text{leaf}$

- $n(T) = 1$이고 $h(T) = 0$이다
- $2^{0+1} - 1 = 2 - 1 = 1 ≥ 1$ ✓

**귀납적 단계**: $T = \text{node}(T_1, T_2)$

- 귀납 가정: $n(T_1) ≤ 2^{h(T_1)+1} - 1$과 $n(T_2) ≤ 2^{h(T_2)+1} - 1$
- $n(T) = 1 + n(T_1) + n(T_2)$
- $h(T) = 1 + \max(h(T_1), h(T_2))$
- $n(T) ≤ 1 + (2^{h(T_1)+1} - 1) + (2^{h(T_2)+1} - 1)$
- $≤ 2 \cdot \max(2^{h(T_1)+1}, 2^{h(T_2)+1}) - 1$
- $= 2^{h(T)+1} - 1$ ✓

### Lean4로 구체적 확인

```lean
-- 구체적 트리에서 부등식 확인
-- t1: numNodes = 3, height = 1, 2^(1+1) - 1 = 3
example : t1.numNodes ≤ 2 ^ (t1.height + 1) - 1 := by native_decide

-- t2: numNodes = 5, height = 2, 2^(2+1) - 1 = 7
example : t2.numNodes ≤ 2 ^ (t2.height + 1) - 1 := by native_decide

-- 균형 잡힌 높이 3 트리
def t3 : FullBinTree :=
  .node (.node (.node .leaf .leaf) (.node .leaf .leaf))
        (.node (.node .leaf .leaf) (.node .leaf .leaf))

-- numNodes = 15, height = 3, 2^4 - 1 = 15 (등호 성립!)
example : t3.numNodes ≤ 2 ^ (t3.height + 1) - 1 := by native_decide
```

> 💡 **등호가 성립하는 경우**: 완전히 **균형 잡힌** 포화 이진 트리에서 등호가 성립한다. 이때 꼭짓점 수는 정확히 $2^{h+1} - 1$이다.

### 연습 5-1: 정리의 구체적 확인 (sorry 채우기)

```lean
-- 불균형 트리
def t4 : FullBinTree :=
  .node (.node (.node .leaf .leaf) .leaf) .leaf

-- 꼭짓점 수와 높이 확인
example : t4.numNodes = 7 := by sorry
example : t4.height = 3 := by sorry

-- 부등식 확인: 7 ≤ 2^4 - 1 = 15
example : t4.numNodes ≤ 2 ^ (t4.height + 1) - 1 := by sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
example : t4.numNodes = 7 := by rfl
example : t4.height = 3 := by rfl
example : t4.numNodes ≤ 2 ^ (t4.height + 1) - 1 := by native_decide
```

**설명**: `t4`는 왼쪽으로 치우친 불균형 트리이다. 높이 3에 꼭짓점 7개인데, 균형 트리라면 15개까지 가능하다. 따라서 $7 ≤ 15$이 성립한다.

</details>

---

## 8E.6 구조적 귀납법 증명 연습

### 연습 6-1: 잎의 수 세기

포화 이진 트리에서 **잎**(leaf)의 수를 세는 함수를 정의하자:

```lean
def FullBinTree.numLeaves : FullBinTree → Nat
  | .leaf => 1                          -- 잎 자체는 잎 1개
  | .node l r => l.numLeaves + r.numLeaves  -- 잎의 수 = 왼 + 오

-- 확인
example : t0.numLeaves = 1 := by rfl
example : t1.numLeaves = 2 := by rfl
```

### 연습 6-2: 내부 꼭짓점 수 (괄호 채우기)

**내부 꼭짓점**(internal vertex)은 잎이 아닌 꼭짓점이다:

```lean
def FullBinTree.numInternal : FullBinTree → Nat
  | .leaf => (______)                             -- 잎은 내부 꼭짓점이 아님
  | .node l r => 1 + l.numInternal + r.numInternal  -- 노드 + 왼 + 오

-- numInternal = numNodes - numLeaves
example : t1.numInternal = (______) := by rfl  -- 1
example : t2.numInternal = (______) := by rfl  -- 2
```

<details>
<summary>💡 답 보기</summary>

```lean
def FullBinTree.numInternal : FullBinTree → Nat
  | .leaf => 0
  | .node l r => 1 + l.numInternal + r.numInternal

example : t1.numInternal = 1 := by rfl
example : t2.numInternal = 2 := by rfl
```

</details>

### 연습 6-3: "잎의 수 = 내부 꼭짓점 수 + 1" (Rosen 연습 45, 46 관련)

포화 이진 트리에서 $\text{numLeaves}(T) = \text{numInternal}(T) + 1$이다!

구체적으로 확인:

```lean
-- t0: 잎 1, 내부 0 → 1 = 0 + 1 ✓
-- t1: 잎 2, 내부 1 → 2 = 1 + 1 ✓
-- t2: 잎 3, 내부 2 → 3 = 2 + 1 ✓
-- t3: 잎 8, 내부 7 → 8 = 7 + 1 ✓

-- 연습: 확인 (sorry 채우기)
example : t3.numLeaves = t3.numInternal + 1 := by sorry
example : t4.numLeaves = t4.numInternal + 1 := by sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
example : t3.numLeaves = t3.numInternal + 1 := by native_decide
example : t4.numLeaves = t4.numInternal + 1 := by native_decide
```

**구조적 귀납법 증명 아이디어**:

- **기본**: leaf → numLeaves = 1 = 0 + 1 = numInternal + 1 ✓
- **귀납**: $T = \text{node}(T_1, T_2)$라 하고, 
  - 귀납 가정: $L_1 = I_1 + 1$, $L_2 = I_2 + 1$
  - $L = L_1 + L_2 = (I_1 + 1) + (I_2 + 1) = (1 + I_1 + I_2) + 1 = I + 1$ ✓

</details>

### 연습 6-4: 구조적 귀납법으로 정식 증명 (도전)

```lean
-- 잎의 수 = 내부 꼭짓점 수 + 1 (구조적 귀납법)
theorem leaves_eq_internal_plus_one (t : FullBinTree) :
    t.numLeaves = t.numInternal + 1 := by
  induction t with
  | leaf =>
    -- 기본 단계: leaf
    sorry
  | node l r ihl ihr =>
    -- 귀납적 단계: node l r
    -- ihl : l.numLeaves = l.numInternal + 1
    -- ihr : r.numLeaves = r.numInternal + 1
    sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
theorem leaves_eq_internal_plus_one (t : FullBinTree) :
    t.numLeaves = t.numInternal + 1 := by
  induction t with
  | leaf =>
    rfl  -- 1 = 0 + 1
  | node l r ihl ihr =>
    simp [FullBinTree.numLeaves, FullBinTree.numInternal]
    rw [ihl, ihr]
    omega
```

**증명 해설**:

1. `induction t with` — `t`에 대한 구조적 귀납법 시작
2. `| leaf =>` — 기본 단계: `numLeaves leaf = 1 = 0 + 1 = numInternal leaf + 1`
3. `| node l r ihl ihr =>` — 귀납적 단계:
   - `ihl : l.numLeaves = l.numInternal + 1` (왼쪽 부분트리에 대한 귀납 가정)
   - `ihr : r.numLeaves = r.numInternal + 1` (오른쪽 부분트리에 대한 귀납 가정)
4. `simp` — 정의를 펼친다
5. `rw [ihl, ihr]` — 귀납 가정으로 치환
6. `omega` — 산술 계산: $(I_1 + 1) + (I_2 + 1) = (1 + I_1 + I_2) + 1$

</details>

---

## 8E.7 문자열에 대한 구조적 귀납법 (Rosen 예제 12)

### 문자열 길이의 덧셈 공식

Rosen 예제 12: 알파벳 Σ에 대한 문자열 $x, y ∈ Σ^*$에 대해, 구조적 귀납법으로 $l(xy) = l(x) + l(y)$임을 증명하라.

Lean4에서 문자열은 `List`이고, 길이는 `List.length`이다:

```lean
-- Lean4에서 이미 증명되어 있다:
-- List.length_append : (xs ++ ys).length = xs.length + ys.length

-- 직접 정의한 myLength로 연습
def myLength : List α → Nat
  | [] => 0
  | _ :: as => 1 + myLength as

-- 구조적 귀납법으로 증명
theorem myLength_append (xs ys : List α) :
    myLength (xs ++ ys) = myLength xs + myLength ys := by
  induction xs with
  | nil =>
    simp [myLength]  -- myLength [] + myLength ys = 0 + myLength ys
  | cons a as ih =>
    simp [myLength]  -- 정의 펼치기
    rw [ih]          -- 귀납 가정 적용
    omega            -- 1 + (myLength as + myLength ys) = (1 + myLength as) + myLength ys
```

### 연습 7-1: 리스트 뒤집기 길이 보존 (sorry 채우기)

```lean
def myReverse : List α → List α
  | [] => []
  | a :: as => myReverse as ++ [a]

-- 뒤집어도 길이가 같다
theorem myReverse_length (xs : List α) :
    myLength (myReverse xs) = myLength xs := by
  induction xs with
  | nil =>
    sorry  -- 기본 단계
  | cons a as ih =>
    sorry  -- 귀납적 단계
```

<details>
<summary>💡 답 보기</summary>

```lean
theorem myReverse_length (xs : List α) :
    myLength (myReverse xs) = myLength xs := by
  induction xs with
  | nil =>
    rfl
  | cons a as ih =>
    simp [myReverse, myLength_append, myLength]
    rw [ih]
```

**증명 구조**:
- 기본: `myReverse [] = []` → `myLength [] = 0 = myLength []`
- 귀납: `myReverse (a :: as) = myReverse as ++ [a]`
  - `myLength (myReverse as ++ [a]) = myLength (myReverse as) + myLength [a]` (append 정리)
  - `= myLength as + 1` (귀납 가정 + myLength [a] = 1)
  - `= myLength (a :: as)` (myLength 정의)

</details>

---

## 8E.8 체계화 공식과 구조적 귀납법 (Rosen 예제 11)

### 명제 논리의 체계화 공식

Rosen 예제 8에서 정의한 **체계화 공식**(well-formed formulae):

- **기본 단계**: $s$가 명제 변수일 때, **T**, **F**, $s$는 체계화 공식
- **재귀적 단계**: $E$와 $F$가 체계화 공식이면, $(\neg E)$, $(E \wedge F)$, $(E \vee F)$, $(E \rightarrow F)$, $(E \leftrightarrow F)$도 체계화 공식

### 정리: 동일한 수의 왼쪽·오른쪽 괄호 (Rosen 예제 11)

모든 체계화 공식이 **동일한 수의 왼쪽 괄호와 오른쪽 괄호**를 포함한다는 것을 구조적 귀납법으로 보인다.

```lean
-- 간단한 명제 공식 타입
inductive PropFormula where
  | var : String → PropFormula             -- 변수
  | not : PropFormula → PropFormula        -- ¬E
  | and : PropFormula → PropFormula → PropFormula  -- E ∧ F
  | or  : PropFormula → PropFormula → PropFormula  -- E ∨ F
  deriving Repr

-- 왼쪽 괄호 수
def PropFormula.leftParens : PropFormula → Nat
  | .var _ => 0
  | .not e => 1 + e.leftParens          -- (¬E)는 괄호 1개 추가
  | .and e f => 1 + e.leftParens + f.leftParens
  | .or e f => 1 + e.leftParens + f.leftParens

-- 오른쪽 괄호 수
def PropFormula.rightParens : PropFormula → Nat
  | .var _ => 0
  | .not e => 1 + e.rightParens
  | .and e f => 1 + e.rightParens + f.rightParens
  | .or e f => 1 + e.rightParens + f.rightParens
```

### 연습 8-1: 괄호 수 확인 (괄호 채우기)

```lean
def p := PropFormula.var "p"
def q := PropFormula.var "q"
def f1 := PropFormula.and p q              -- (p ∧ q)
def f2 := PropFormula.or (PropFormula.not p) q  -- ((¬p) ∨ q)

example : f1.leftParens = (______) := by rfl
example : f1.rightParens = (______) := by rfl
example : f2.leftParens = (______) := by rfl
example : f2.rightParens = (______) := by rfl
```

<details>
<summary>💡 답 보기</summary>

```lean
example : f1.leftParens = 1 := by rfl
example : f1.rightParens = 1 := by rfl
example : f2.leftParens = 2 := by rfl   -- or 1개 + not 1개
example : f2.rightParens = 2 := by rfl
```

</details>

### 연습 8-2: 왼쪽 = 오른쪽 괄호 증명 (도전)

```lean
-- 모든 체계화 공식에서 왼쪽 괄호 수 = 오른쪽 괄호 수
theorem parens_equal (f : PropFormula) :
    f.leftParens = f.rightParens := by
  induction f with
  | var s =>
    sorry  -- 기본: 변수에 괄호 없음
  | not e ih =>
    sorry  -- 1 + e.leftParens = 1 + e.rightParens
  | and e f ihe ihf =>
    sorry  -- 1 + e.left + f.left = 1 + e.right + f.right
  | or e f ihe ihf =>
    sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
theorem parens_equal (f : PropFormula) :
    f.leftParens = f.rightParens := by
  induction f with
  | var s => rfl
  | not e ih =>
    simp [PropFormula.leftParens, PropFormula.rightParens]
    exact ih
  | and e f ihe ihf =>
    simp [PropFormula.leftParens, PropFormula.rightParens]
    omega
  | or e f ihe ihf =>
    simp [PropFormula.leftParens, PropFormula.rightParens]
    omega
```

**증명 해설**:
- `var`: 양쪽 다 0이므로 `rfl`
- `not e ih`: `1 + e.leftParens = 1 + e.rightParens`인데, `ih`에 의해 `e.leftParens = e.rightParens`
- `and e f ihe ihf`: `1 + e.L + f.L = 1 + e.R + f.R`인데, `ihe`와 `ihf`에 의해 성립

</details>

---

## 8E.9 일반화된 귀납법 미리보기 (Rosen 5.3.5)

### 사전순 정렬에 대한 귀납법

자연수 집합 외의 다른 집합에 **순서화 성질**(well-ordering)을 갖는 경우에도 귀납법을 확장할 수 있다.

예: $\mathbb{N} \times \mathbb{N}$의 **사전순 정렬**(lexicographic ordering)

$(x_1, y_1) < (x_2, y_2)$ ⟺ $x_1 < x_2$이거나 ($x_1 = x_2$이고 $y_1 < y_2$)

```lean
-- Lean4에서 사전순 비교
-- Prod.Lex 관계가 이를 제공

-- 예: (1, 3) < (2, 0) (첫 번째 좌표가 작으므로)
-- 예: (2, 1) < (2, 3) (첫 번째 같고 두 번째가 작으므로)

-- 구체적 확인
example : (1 : Nat) < 2 := by omega
example : (1, 3) < (2, 0) := by
  constructor  -- Prod.lt는 (fst < fst) 또는 (fst = fst ∧ snd < snd)
  omega
```

> 이 주제는 Rosen 9.6절에서 더 자세히 다루며, 여기서는 개념만 소개한다.

---

## 8E.10 전술 및 개념 종합 요약

### 구조적 귀납법 핵심

| 개념 | 설명 |
|------|------|
| **구조적 귀납법** | 재귀적으로 정의된 집합의 원소에 대한 귀납법 |
| **기본 단계** | 기본 생성자(leaf, nil, var)에 대해 성립 증명 |
| **귀납적 단계** | 재귀 생성자(node, cons, not/and/or)에 대해 성립 증명 |
| `induction t with` | Lean4에서 구조적 귀납법 시작 |
| `\| leaf =>` | 기본 경우 |
| `\| node l r ihl ihr =>` | 재귀 경우 (`ihl`, `ihr`은 귀납 가정) |

### 이 파트에서 정의한 타입

| 타입 | 생성자 | 용도 |
|------|---------|------|
| `FullBinTree` | `leaf`, `node l r` | 포화 이진 트리 |
| `PropFormula` | `var`, `not`, `and`, `or` | 명제 논리 공식 |

### 이 파트에서 증명한 정리

| 정리 | 내용 | 증명 방법 |
|------|------|---------|
| $n(T) ≤ 2^{h(T)+1} - 1$ | 포화 이진 트리의 꼭짓점 수 상한 | 구조적 귀납법 |
| $L(T) = I(T) + 1$ | 잎 수 = 내부 꼭짓점 수 + 1 | 구조적 귀납법 |
| $l(xy) = l(x) + l(y)$ | 문자열 길이의 덧셈 | 구조적 귀납법 (리스트) |
| 왼쪽 괄호 = 오른쪽 괄호 | 체계화 공식의 괄호 균형 | 구조적 귀납법 |

---

## 다음 편(8-F) 예고

다음 편에서는:
- **재귀 알고리즘**(Recursive Algorithms) — Rosen 5.4절
- **팩토리얼**, **거듭제곱**, **최대공약수**의 재귀 알고리즘
- **병합 정렬**(Merge Sort)의 재귀적 구현
- **재귀 알고리즘의 정확성** 증명

을 다룬다.

---

**(끝)**
