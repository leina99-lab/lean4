# Lean4 Tutorial Part 6-B: **알고리즘**(Algorithms)과 Lean4 — 심화편

> **기반 교재**: Kenneth H. Rosen, *Discrete Mathematics and Its Applications* 8판 3.1절  
> **참고 교재**: *Mathematics in Lean* Chapter 5, 6  
> **선수 지식**: Part 6-A (함수 정의, 리스트, 선형 탐색, →와 ↔의 차이)

---

## 6B.0 이 파트에서 배우는 것

이 파트에서는 다음을 학습한다:

1. **이진 탐색**(binary search) — 정렬된 리스트에서 효율적으로 찾기
2. **정렬**(sorting) 알고리즘 — 버블 정렬(bubble sort)과 삽입 정렬(insertion sort)
3. **문자열 매칭**(string matching) — 패턴이 텍스트에 나오는지 찾기
4. **욕심쟁이 알고리즘**(greedy algorithm) — 매 단계에서 최선의 선택
5. **정지 문제**(halting problem) — 풀 수 없는 문제도 있다!
6. **귀납법**(induction)으로 알고리즘의 정확성을 증명하기

---

## 6B.1 **이진 탐색**(Binary Search) — Rosen 알고리즘 3

### 아이디어

선형 탐색은 리스트의 원소를 **하나씩** 확인한다. 만약 리스트가 **오름차순으로 정렬**되어 있다면, 훨씬 효율적인 방법이 있다.

이진 탐색의 핵심 아이디어: **가운데 원소**와 비교하여 **반씩 줄여나간다**.

1. 리스트의 가운데 원소를 확인한다
2. 찾으려는 값이 가운데 원소와 **같으면** → 찾았다!
3. 찾으려는 값이 가운데 원소보다 **작으면** → 왼쪽 절반에서만 계속 찾는다
4. 찾으려는 값이 가운데 원소보다 **크면** → 오른쪽 절반에서만 계속 찾는다

### 교재의 의사 코드 (Rosen 알고리즘 3)

```
procedure binary search(x: integer, a₁, a₂, ..., aₙ: increasing integers)
i := 1
j := n
while i < j
    m := ⌊(i + j)/2⌋
    if x > aₘ then i := m + 1
    else j := m
if x = aᵢ then location := i
else location := 0
return location
```

### 교재의 예제 3: 19 찾기

교재에서는 다음 정렬된 리스트에서 19를 찾는 과정을 보여준다:

```
리스트: 1 2 3 5 6 7 8 10 12 13 15 16 18 19 20 22
```

**1단계**: 전체 리스트 (16개 원소)를 반으로 나눈다
- 왼쪽: 1 2 3 5 6 7 8 10
- 오른쪽: 12 13 15 16 18 19 20 22
- 가운데 원소: 10 (8번째)
- 19 > 10 → 오른쪽 반에서 계속

**2단계**: 오른쪽 반 (8개 원소)을 다시 반으로 나눈다
- 왼쪽: 12 13 15 16
- 오른쪽: 18 19 20 22
- 가운데 원소: 16 (4번째)
- 19 > 16 → 오른쪽 반에서 계속

**3단계**: 오른쪽 반 (4개 원소)을 다시 반으로 나눈다
- 왼쪽: 18 19
- 오른쪽: 20 22
- 가운데 원소: 19 (2번째)
- 19 ≤ 19 → 왼쪽 반에서 계속

**4단계**: 왼쪽 반 (2개 원소)을 다시 반으로 나눈다
- 왼쪽: 18
- 오른쪽: 19
- 가운데 원소: 18
- 19 > 18 → 오른쪽으로

**5단계**: 원소 하나 남음 (19)
- 19 = 19 → **찾았다!** 위치는 14번째

### Lean4로 구현하기

Lean4에서 이진 탐색을 구현하는 방법은 여러 가지가 있다. 여기서는 `Array`를 사용한 버전을 보여준다:

```lean
-- 배열(Array)에서 이진 탐색
-- 정렬된 배열에서 값 x를 찾아 인덱스를 반환
def binarySearch (arr : Array Nat) (x : Nat) : Option Nat :=
  go 0 arr.size
where
  go (lo hi : Nat) : Option Nat :=
    if lo ≥ hi then none
    else
      let mid := (lo + hi) / 2
      if h : mid < arr.size then
        let v := arr[mid]
        if x == v then some mid
        else if x < v then go lo mid
        else go (mid + 1) hi
      else none
  termination_by hi - lo
```

이 코드를 부분별로 분석하자:

**`def binarySearch (arr : Array Nat) (x : Nat) : Option Nat`**
- `arr` : 정렬된 자연수 배열
- `x` : 찾으려는 값
- `Option Nat` : 찾으면 `some 인덱스`, 못 찾으면 `none`

**`go (lo hi : Nat)`**
- `lo` : 탐색 범위의 왼쪽 끝 (포함)
- `hi` : 탐색 범위의 오른쪽 끝 (미포함)
- 이것은 교재의 `i`와 `j`에 해당한다

**`let mid := (lo + hi) / 2`**
- 가운데 인덱스를 계산한다
- 교재의 `m := ⌊(i + j)/2⌋`에 해당한다

**`termination_by hi - lo`**
- Lean4의 종료 검사기에게 "매번 `hi - lo`가 줄어들므로 이 함수는 반드시 멈춘다"고 알려준다
- 이것은 알고리즘의 **유한성**(finiteness) 속성을 보장한다

### 리스트 버전 (더 간단)

배열 대신 리스트로 구현하면 더 간단하지만, 효율성은 떨어진다. 개념 이해를 위한 버전이다:

```lean
-- 정렬된 리스트에서 값이 있는지 확인 (이진 탐색의 정신)
-- 실제로는 리스트를 반으로 자르는 것이 비효율적이지만, 개념 학습용
def sortedContains : Nat → List Nat → Bool
  | _, []      => false
  | x, [a]    => x == a
  | x, xs     =>
    let mid := xs.length / 2
    let midVal := xs.get! mid   -- mid번째 원소
    if x == midVal then true
    else if x < midVal then sortedContains x (xs.take mid)
    else sortedContains x (xs.drop (mid + 1))

#eval sortedContains 19 [1, 2, 3, 5, 6, 7, 8, 10, 12, 13, 15, 16, 18, 19, 20, 22]
-- true

#eval sortedContains 11 [1, 2, 3, 5, 6, 7, 8, 10, 12, 13, 15, 16, 18, 19, 20, 22]
-- false
```

### 선형 탐색 vs 이진 탐색

| 비교 항목 | **선형 탐색**(linear search) | **이진 탐색**(binary search) |
|-----------|--------------------------|--------------------------|
| 입력 조건 | 아무 리스트 | **정렬된** 리스트만 |
| 최악의 비교 횟수 | n번 | ⌈log₂ n⌉번 |
| n = 16일 때 | 최대 16번 | 최대 4번 |
| n = 1,000,000일 때 | 최대 1,000,000번 | 최대 20번 |

이 차이가 매우 크다! 백만 개의 원소에서 찾을 때, 선형 탐색은 최악의 경우 백만 번 비교해야 하지만, 이진 탐색은 고작 20번이면 충분하다.

---

## 6B.2 연습문제 세트 5: 탐색 알고리즘

### 연습 5-1: 이진 탐색 추적 (Rosen 연습문제 13)

다음 정렬된 리스트에서 이진 탐색으로 **9**를 찾는 모든 단계를 보여라.

리스트: `1, 3, 4, 5, 6, 8, 9, 11`

```lean
#eval sortedContains 9 [1, 3, 4, 5, 6, 8, 9, 11]  -- true
```

<details>
<summary>💡 답 보기</summary>

**1단계**: 전체 리스트 [1, 3, 4, 5, 6, 8, 9, 11], 길이 8
- mid = 8/2 = 4, midVal = 리스트[4] = 6
- 9 > 6 → 오른쪽 반 [8, 9, 11]에서 계속

**2단계**: [8, 9, 11], 길이 3
- mid = 3/2 = 1, midVal = 리스트[1] = 9
- 9 == 9 → **찾았다!**

총 비교 횟수: **2번**

선형 탐색이었다면 7번 비교했을 것이다 (9가 7번째 원소이므로).

</details>

---

### 연습 5-2: 이진 탐색으로 7 찾기 (Rosen 연습문제 13 변형)

같은 리스트에서 **7**을 이진 탐색으로 찾아보라. 7은 리스트에 없다.

```lean
#eval sortedContains 7 [1, 3, 4, 5, 6, 8, 9, 11]  -- false
```

<details>
<summary>💡 답 보기</summary>

**1단계**: [1, 3, 4, 5, 6, 8, 9, 11], 길이 8
- mid = 4, midVal = 6
- 7 > 6 → 오른쪽 반 [8, 9, 11]

**2단계**: [8, 9, 11], 길이 3
- mid = 1, midVal = 9
- 7 < 9 → 왼쪽 반 [8]

**3단계**: [8], 길이 1
- 7 == 8? 아니다 → **못 찾음** (none/false)

총 비교 횟수: **3번**

</details>

---

## 6B.3 **버블 정렬**(Bubble Sort) — Rosen 알고리즘 4

### 아이디어

**버블 정렬**은 정렬 알고리즘 중 가장 간단한 것이다. 인접한 원소를 비교하여, 순서가 잘못되어 있으면 서로 교환한다. 이 과정을 반복하면 큰 원소가 "거품"처럼 위로 떠오른다.

### 교재의 의사 코드 (Rosen 알고리즘 4)

```
procedure bubblesort(a₁, ..., aₙ : real numbers with n ≥ 2)
for i := 1 to n - 1
    for j := 1 to n - i
        if aⱼ > aⱼ₊₁ then interchange aⱼ and aⱼ₊₁
{a₁, ..., aₙ is in increasing order}
```

### 교재의 예제 4: 버블 정렬로 3, 2, 4, 1, 5 정렬하기

**First pass** (첫 번째 순회):
- 3과 2 비교: 3 > 2 → 교환 → [2, 3, 4, 1, 5]
- 3과 4 비교: 3 < 4 → 교환 안 함
- 4와 1 비교: 4 > 1 → 교환 → [2, 3, 1, 4, 5]
- 4와 5 비교: 4 < 5 → 교환 안 함
- 결과: [2, 3, 1, 4, 5] (5가 제자리에 왔다)

**Second pass** (두 번째 순회):
- 2와 3 비교: 2 < 3 → 교환 안 함
- 3과 1 비교: 3 > 1 → 교환 → [2, 1, 3, 4, 5]
- 3과 4 비교: 3 < 4 → 교환 안 함
- 결과: [2, 1, 3, 4, 5] (4, 5가 제자리에 왔다)

**Third pass** (세 번째 순회):
- 2와 1 비교: 2 > 1 → 교환 → [1, 2, 3, 4, 5]
- 2와 3 비교: 2 < 3 → 교환 안 함
- 결과: [1, 2, 3, 4, 5] (3, 4, 5가 제자리에 왔다)

**Fourth pass** (네 번째 순회):
- 1과 2 비교: 1 < 2 → 교환 안 함
- 결과: [1, 2, 3, 4, 5] (**정렬 완료!**)

### Lean4로 구현하기

```lean
-- 한 번의 패스: 리스트를 한 번 훑으면서 인접한 원소를 정렬
def bubblePass : List Nat → List Nat
  | []          => []
  | [a]         => [a]
  | a :: b :: rest =>
      if a > b then b :: bubblePass (a :: rest)   -- 교환 후 계속
      else a :: bubblePass (b :: rest)             -- 교환 안 하고 계속

-- 버블 정렬: 패스를 n-1번 반복
def bubbleSort (xs : List Nat) : List Nat :=
  go xs xs.length
where
  go (xs : List Nat) : Nat → List Nat
    | 0     => xs
    | n + 1 => go (bubblePass xs) n

#eval bubbleSort [3, 2, 4, 1, 5]  -- [1, 2, 3, 4, 5]
#eval bubbleSort [5, 4, 3, 2, 1]  -- [1, 2, 3, 4, 5]
#eval bubbleSort [1, 2, 3]        -- [1, 2, 3]
#eval bubbleSort []                -- []
```

### 각 단계를 추적하는 버전

```lean
-- 각 패스의 결과를 기록
def bubbleSortTrace (xs : List Nat) : List (List Nat) :=
  go xs xs.length [xs]
where
  go (xs : List Nat) : Nat → List (List Nat) → List (List Nat)
    | 0, acc     => acc
    | n + 1, acc =>
      let next := bubblePass xs
      go next n (acc ++ [next])

#eval bubbleSortTrace [3, 2, 4, 1, 5]
-- [[3, 2, 4, 1, 5], [2, 3, 1, 4, 5], [2, 1, 3, 4, 5], [1, 2, 3, 4, 5], ...]
```

---

## 6B.4 **삽입 정렬**(Insertion Sort) — Rosen 알고리즘 5

### 아이디어

**삽입 정렬**은 카드 놀이에서 패를 정리하는 것과 같다. 왼손에 이미 정렬된 카드가 있고, 오른손에서 새 카드를 하나 가져와서 왼손의 올바른 위치에 **삽입**한다.

### Lean4로 구현하기

```lean
-- 정렬된 리스트에 원소 하나를 올바른 위치에 삽입
def insert (x : Nat) : List Nat → List Nat
  | []      => [x]
  | a :: as => if x ≤ a then x :: a :: as
               else a :: insert x as

-- 삽입 정렬: 빈 리스트에서 시작하여 하나씩 삽입
def insertionSort : List Nat → List Nat
  | []      => []
  | a :: as => insert a (insertionSort as)

#eval insertionSort [3, 2, 4, 1, 5]  -- [1, 2, 3, 4, 5]
#eval insertionSort [5, 4, 3, 2, 1]  -- [1, 2, 3, 4, 5]
```

### 교재의 예제 5: 삽입 정렬로 3, 2, 4, 1, 5 정렬하기

```
시작: 아직 정렬된 부분 없음

1단계: 2와 3 비교 → 2, 3    정렬된 부분: [2, 3]
2단계: 4를 삽입 → 2, 3, 4   정렬된 부분: [2, 3, 4]
3단계: 1을 삽입 → 1, 2, 3, 4  정렬된 부분: [1, 2, 3, 4]
4단계: 5를 삽입 → 1, 2, 3, 4, 5  완료!
```

Lean4 코드의 동작 추적:

```
insertionSort [3, 2, 4, 1, 5]
= insert 3 (insertionSort [2, 4, 1, 5])
= insert 3 (insert 2 (insertionSort [4, 1, 5]))
= insert 3 (insert 2 (insert 4 (insertionSort [1, 5])))
= insert 3 (insert 2 (insert 4 (insert 1 (insertionSort [5]))))
= insert 3 (insert 2 (insert 4 (insert 1 (insert 5 []))))
= insert 3 (insert 2 (insert 4 (insert 1 [5])))
= insert 3 (insert 2 (insert 4 [1, 5]))
= insert 3 (insert 2 [1, 4, 5])
= insert 3 [1, 2, 4, 5]
= [1, 2, 3, 4, 5]
```

### `insert` 함수의 정확성

`insert` 함수가 올바르게 동작한다는 것은 다음 성질로 표현할 수 있다: "정렬된 리스트에 원소를 삽입한 결과도 정렬되어 있다."

이것을 증명하려면 **귀납법**(induction)이 필요하다. 귀납법은 Part 4-6에서 배우는 내용이지만, 여기서 간단한 예를 미리 보자:

```lean
-- 정렬되어 있는지 판별하는 함수
def isSorted : List Nat → Bool
  | []          => true
  | [_]         => true
  | a :: b :: rest => a ≤ b && isSorted (b :: rest)

#eval isSorted [1, 2, 3, 4, 5]  -- true
#eval isSorted [1, 3, 2, 4]     -- false
#eval isSorted []                 -- true
```

```lean
-- insert가 정렬을 유지한다는 것을 몇 가지 예시로 확인
#eval isSorted (insert 3 [1, 2, 4, 5])  -- true ([1, 2, 3, 4, 5])
#eval isSorted (insert 0 [1, 2, 3])     -- true ([0, 1, 2, 3])
#eval isSorted (insert 99 [1, 2, 3])    -- true ([1, 2, 3, 99])
```

---

## 6B.5 연습문제 세트 6: 정렬 알고리즘

### 연습 6-1: 버블 정렬 추적 (Rosen 연습문제 36)

버블 정렬을 이용하여 `6, 2, 3, 1, 5, 4`를 정렬하고, 각 단계별 결과를 보여라.

```lean
#eval bubbleSortTrace [6, 2, 3, 1, 5, 4]
```

<details>
<summary>💡 답 보기</summary>

**Pass 1**: [6, 2, 3, 1, 5, 4]
- 6 > 2 → 교환 → [2, 6, 3, 1, 5, 4]
- 6 > 3 → 교환 → [2, 3, 6, 1, 5, 4]
- 6 > 1 → 교환 → [2, 3, 1, 6, 5, 4]
- 6 > 5 → 교환 → [2, 3, 1, 5, 6, 4]
- 6 > 4 → 교환 → [2, 3, 1, 5, 4, 6]
→ 결과: **[2, 3, 1, 5, 4, 6]**

**Pass 2**: [2, 3, 1, 5, 4, 6]
- 2 < 3 → 유지
- 3 > 1 → 교환 → [2, 1, 3, 5, 4, 6]
- 3 < 5 → 유지
- 5 > 4 → 교환 → [2, 1, 3, 4, 5, 6]
→ 결과: **[2, 1, 3, 4, 5, 6]**

**Pass 3**: [2, 1, 3, 4, 5, 6]
- 2 > 1 → 교환 → [1, 2, 3, 4, 5, 6]
→ 결과: **[1, 2, 3, 4, 5, 6]**

**Pass 4, 5**: 변화 없음. 최종 결과: **[1, 2, 3, 4, 5, 6]**

Lean4 확인:
```lean
#eval bubbleSort [6, 2, 3, 1, 5, 4]  -- [1, 2, 3, 4, 5, 6]
```

</details>

---

### 연습 6-2: 삽입 정렬 추적 (Rosen 연습문제 40)

삽입 정렬을 이용하여 같은 리스트 `6, 2, 3, 1, 5, 4`를 정렬하고, 각 단계별 결과를 보여라.

<details>
<summary>💡 답 보기</summary>

**1단계**: 2를 [6]에 삽입 → 2 ≤ 6이므로 앞에 → **[2, 6]**
**2단계**: 3을 [2, 6]에 삽입 → 3 > 2, 3 ≤ 6 → **[2, 3, 6]**
**3단계**: 1을 [2, 3, 6]에 삽입 → 1 ≤ 2이므로 맨 앞 → **[1, 2, 3, 6]**
**4단계**: 5를 [1, 2, 3, 6]에 삽입 → 5 > 3, 5 ≤ 6 → **[1, 2, 3, 5, 6]**
**5단계**: 4를 [1, 2, 3, 5, 6]에 삽입 → 4 > 3, 4 ≤ 5 → **[1, 2, 3, 4, 5, 6]**

Lean4 확인:
```lean
#eval insertionSort [6, 2, 3, 1, 5, 4]  -- [1, 2, 3, 4, 5, 6]
```

</details>

---

### 연습 6-3: `insert` 함수 구현 (sorry 채우기)

정렬된 리스트에 원소를 올바른 위치에 삽입하는 함수를 완성하라.

```lean
def myInsert (x : Nat) : List Nat → List Nat
  | []      => sorry
  | a :: as => if x ≤ a then sorry
               else sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
def myInsert (x : Nat) : List Nat → List Nat
  | []      => [x]
  | a :: as => if x ≤ a then x :: a :: as
               else a :: myInsert x as
```

**설명**:
- 빈 리스트에 삽입 → `[x]`
- `x ≤ a`이면 x를 맨 앞에 놓는다 (올바른 위치를 찾았다)
- `x > a`이면 a를 그대로 두고 나머지 리스트에서 올바른 위치를 찾는다

테스트:
```lean
#eval myInsert 3 [1, 2, 4, 5]  -- [1, 2, 3, 4, 5]
#eval myInsert 0 [1, 2, 3]     -- [0, 1, 2, 3]
#eval myInsert 99 [1, 2, 3]    -- [1, 2, 3, 99]
```

</details>

---

### 연습 6-4: `isSorted` 판별 함수 (sorry 채우기)

리스트가 오름차순으로 정렬되어 있는지 판별하는 함수를 완성하라.

```lean
def mySorted : List Nat → Bool
  | []              => sorry
  | [_]             => sorry
  | a :: b :: rest  => sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
def mySorted : List Nat → Bool
  | []              => true
  | [_]             => true
  | a :: b :: rest  => a ≤ b && mySorted (b :: rest)
```

**설명**:
- 빈 리스트는 (자명하게) 정렬되어 있다
- 원소가 하나인 리스트도 정렬되어 있다
- 두 개 이상이면: 첫 두 원소가 순서대로이고(`a ≤ b`) 나머지도 정렬되어 있어야 한다

테스트:
```lean
#eval mySorted [1, 2, 3, 4, 5]  -- true
#eval mySorted [1, 3, 2]         -- false
#eval mySorted [5, 4, 3]         -- false
#eval mySorted [1]               -- true
```

</details>

---

## 6B.6 **문자열 매칭**(String Matching) — Rosen 알고리즘 6

### 아이디어

**문자열 매칭**은 어떤 문자열 P(**패턴**)가 다른 문자열 T(**텍스트**)에 나오는지 찾는 문제이다.

예: 패턴 "eye"가 텍스트 "eceyeye"에 나오는지 찾기

### 교재의 단순 문자열 매칭 알고리즘 (Rosen 알고리즘 6)

가장 단순한 방법은 텍스트의 모든 위치에서 패턴과 비교하는 것이다:

```
procedure string match(n, m, t₁...tₙ, p₁...pₘ)
for s := 0 to n - m
    j := 1
    while (j ≤ m and t_{s+j} = p_j)
        j := j + 1
    if j > m then print "s is a valid shift"
```

### Lean4로 구현하기

자연수 리스트 버전으로 구현한다:

```lean
-- 리스트의 앞부분이 패턴과 일치하는지 확인
def matchPrefix : List Nat → List Nat → Bool
  | _, []           => true    -- 빈 패턴은 항상 일치
  | [], _ :: _      => false   -- 텍스트가 끝났는데 패턴이 남음
  | t :: ts, p :: ps => t == p && matchPrefix ts ps

-- 텍스트에서 패턴이 나타나는 모든 위치를 찾기
def findPattern : List Nat → List Nat → List Nat :=
  go 0
where
  go (pos : Nat) : List Nat → List Nat → List Nat
    | _, []         => []     -- 빈 패턴은 무시
    | [], _         => []     -- 텍스트 끝
    | text, pattern =>
      if text.length < pattern.length then []
      else
        let matches := if matchPrefix text pattern then [pos] else []
        matches ++ go (pos + 1) text.tail pattern

#eval matchPrefix [1, 2, 3] [1, 2]    -- true
#eval matchPrefix [1, 2, 3] [1, 3]    -- false
```

### 교재의 예시: 패턴 "eye" (→ [5, 25, 5])를 텍스트 "eceyeye" (→ [5, 3, 5, 25, 5, 25, 5])에서 찾기

숫자로 치환하여 실행해 보면:

```lean
-- e=5, c=3, y=25로 인코딩
-- 패턴: eye = [5, 25, 5]
-- 텍스트: eceyeye = [5, 3, 5, 25, 5, 25, 5]

#eval matchPrefix [5, 25, 5, 25, 5] [5, 25, 5]  -- true (위치 2에서 시작)
```

---

## 6B.7 **욕심쟁이 알고리즘**(Greedy Algorithm) — Rosen 알고리즘 7

### 아이디어

**욕심쟁이 알고리즘**은 **최적화 문제**(optimization problem)를 풀 때 사용한다. 핵심 전략은: **각 단계에서 가장 좋은 선택**을 한다.

### 교재의 예제 6: 거스름돈 문제

25센트, 10센트, 5센트, 1센트 동전을 가지고, 최소 개수의 동전으로 n센트 거스름돈을 준다.

예: 67센트 거스름돈
1. 25센트 동전 2개 (50센트 사용, 17센트 남음)
2. 10센트 동전 1개 (10센트 사용, 7센트 남음)
3. 5센트 동전 1개 (5센트 사용, 2센트 남음)
4. 1센트 동전 2개 (2센트 사용, 0센트 남음)

총 동전 수: 2 + 1 + 1 + 2 = **6개**

### Lean4로 구현하기

```lean
-- 거스름돈 계산: 각 동전의 개수를 반환
-- coins는 내림차순으로 정렬된 동전 액면가 리스트
def makeChange : List Nat → Nat → List (Nat × Nat)
  | [], _      => []
  | c :: cs, n => (c, n / c) :: makeChange cs (n % c)

-- 미국 동전 시스템
def usCoins : List Nat := [25, 10, 5, 1]

#eval makeChange usCoins 67
-- [(25, 2), (10, 1), (5, 1), (1, 2)]
-- 25센트 2개, 10센트 1개, 5센트 1개, 1센트 2개

#eval makeChange usCoins 30
-- [(25, 1), (10, 0), (5, 1), (1, 0)]
-- 25센트 1개, 5센트 1개 = 총 2개
```

### 욕심쟁이가 항상 최적인가?

**중요한 질문**: 욕심쟁이 알고리즘이 **항상** 최적의 답을 주는가?

**답**: **아니다!** 동전의 종류에 따라 다르다.

미국 동전 시스템(25, 10, 5, 1)에서는 욕심쟁이가 **항상 최적**이라는 것이 증명되어 있다 (Rosen 교재 정리 1). 그러나 다른 동전 시스템에서는 그렇지 않을 수 있다.

```lean
-- 반례: 동전이 25, 10, 1센트뿐이고 (5센트 없음)
-- 30센트 거스름돈
def badCoins : List Nat := [25, 10, 1]

#eval makeChange badCoins 30
-- [(25, 1), (10, 0), (1, 5)] → 25센트 1개 + 1센트 5개 = 6개

-- 하지만 최적은 10센트 3개 = 3개!
-- 욕심쟁이가 최적이 아닌 경우이다
```

---

## 6B.8 연습문제 세트 7: 욕심쟁이와 정렬

### 연습 7-1: 거스름돈 계산 (Rosen 연습문제 56)

계산원 알고리즘을 이용하여 25센트, 10센트, 5센트, 1센트로 다음 거스름돈을 만들어라:

(a) 87센트
(b) 49센트
(c) 99센트
(d) 33센트

```lean
#eval makeChange usCoins 87
#eval makeChange usCoins 49
#eval makeChange usCoins 99
#eval makeChange usCoins 33
```

<details>
<summary>💡 답 보기</summary>

(a) 87센트:
```lean
#eval makeChange usCoins 87  
-- [(25, 3), (10, 1), (5, 0), (1, 2)]
-- 25센트 3개 + 10센트 1개 + 1센트 2개 = 6개
```

(b) 49센트:
```lean
#eval makeChange usCoins 49
-- [(25, 1), (10, 2), (5, 0), (1, 4)]
-- 25센트 1개 + 10센트 2개 + 1센트 4개 = 7개
```

(c) 99센트:
```lean
#eval makeChange usCoins 99
-- [(25, 3), (10, 2), (5, 0), (1, 4)]
-- 25센트 3개 + 10센트 2개 + 1센트 4개 = 9개
```

(d) 33센트:
```lean
#eval makeChange usCoins 33
-- [(25, 1), (10, 0), (5, 1), (1, 3)]
-- 25센트 1개 + 5센트 1개 + 1센트 3개 = 5개
```

</details>

---

### 연습 7-2: 정렬 결과 확인 (전체 작성)

다음 함수는 리스트를 정렬한 후, 결과가 실제로 정렬되어 있는지 확인한다. 직접 작성하라.

```lean
def sortAndCheck (xs : List Nat) : Bool :=
  sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
def sortAndCheck (xs : List Nat) : Bool :=
  isSorted (insertionSort xs)

#eval sortAndCheck [5, 3, 1, 4, 2]    -- true
#eval sortAndCheck [100, 1, 50, 25]   -- true
#eval sortAndCheck []                   -- true
```

이것은 물론 항상 `true`를 반환해야 한다. 만약 `false`가 나온다면 정렬 알고리즘에 버그가 있는 것이다.

</details>

---

## 6B.9 **정지 문제**(Halting Problem) — 풀 수 없는 문제

### 이 절의 중요성

Rosen 교재 3.1.6절은 컴퓨터 과학에서 가장 유명한 결과 중 하나를 다룬다: **정지 문제는 풀 수 없다**.

### 정지 문제란?

**정지 문제**(halting problem): "주어진 프로그램이 주어진 입력에 대해 최종적으로 정지하는지 여부를 결정하는 일반적인 절차가 존재하는가?"

쉽게 말하면: "이 프로그램이 언젠가 끝날까, 아니면 영원히 돌아갈까?"를 판단하는 **만능 프로그램**을 만들 수 있는가?

### 앨런 튜링의 증명 (1936년)

튜링은 **모순에 의한 증명**(proof by contradiction)을 사용했다.

**가정**: 정지 문제를 풀 수 있는 절차 H(P, I)가 존재한다고 하자.
- H(P, I)는 프로그램 P와 입력 I를 받아서
- P가 I를 입력으로 받았을 때 정지하면 "정지"를 출력하고
- 정지하지 않으면 "무한루프"를 출력한다

**모순 유도**: H를 이용하여 새로운 프로그램 K를 만든다.
- K(P)는 H(P, P)의 출력을 확인한다
- H(P, P)가 "무한루프"라면 → K(P)는 정지한다
- H(P, P)가 "정지"라면 → K(P)는 무한루프에 빠진다

**핵심**: K를 K 자신의 입력으로 주면?
- K(K)가 정지한다고 가정하면 → H(K, K) = "정지" → K의 정의에 의해 K(K)는 무한루프 → **모순!**
- K(K)가 정지하지 않는다고 가정하면 → H(K, K) = "무한루프" → K의 정의에 의해 K(K)는 정지 → **모순!**

**결론**: 어느 쪽이든 모순이 발생한다. 따라서 처음 가정인 "H가 존재한다"가 거짓이다. 정지 문제를 풀 수 있는 일반적인 절차는 존재하지 않는다.

### Lean4에서 이 증명의 정신

Lean4에서 정지 문제 자체를 직접 다루기는 어렵지만, "모순에 의한 증명"의 구조는 Lean4에서 자연스럽게 표현된다:

```lean
-- 모순에 의한 증명의 일반적 구조
-- "P가 아니다"를 증명하려면:
-- P를 가정하고 → 모순을 유도한다

example : ¬(∀ n : Nat, n < n) := by
  intro h           -- "모든 자연수 n에 대해 n < n"이라고 가정
  have := h 0       -- 특히 n = 0일 때 0 < 0
  omega              -- 이것은 모순 (0 < 0은 거짓)
```

이 증명의 구조는 튜링의 증명과 같다:
1. 어떤 것이 존재한다고 **가정**한다 (`intro h`)
2. 그 가정으로부터 **구체적인 결과**를 끌어낸다 (`have := h 0`)
3. 그 결과가 **모순**임을 보인다 (`omega`)

### 정지 문제와 Lean4의 종료 검사기

흥미롭게도, Lean4는 **종료 검사기**(termination checker)를 내장하고 있다. 이것은 정지 문제를 "해결"한 것이 아니라, **모든** 프로그램의 종료 여부를 판단하는 것을 포기하고, **특정 형태**의 프로그램만 허용하는 것이다.

Lean4에서 재귀 함수를 정의할 때, Lean4는 "이 함수가 반드시 종료하는가?"를 확인한다. 확인할 수 없으면 컴파일 오류가 발생한다.

```lean
-- 이것은 Lean4가 거부한다: 종료를 보장할 수 없기 때문
-- def loop (n : Nat) : Nat := loop n  -- 오류!

-- 이것은 Lean4가 허용한다: 매번 n이 줄어들므로 종료가 보장됨
def countdown : Nat → List Nat
  | 0     => [0]
  | n + 1 => (n + 1) :: countdown n

#eval countdown 5  -- [5, 4, 3, 2, 1, 0]
```

---

## 6B.10 연습문제 세트 8: 종합 문제

### 연습 8-1: Rosen 연습문제 13a — 선형 탐색으로 9 찾기

수열 1, 3, 4, 5, 6, 8, 9, 11에서 선형 탐색을 사용하여 9를 찾을 때의 모든 단계를 보여라.

```lean
-- 각 단계를 추적하는 선형 탐색
def linearSearchTrace (x : Nat) : List Nat → List (Nat × Bool)
  | []      => []
  | a :: as => (a, x == a) :: (if x == a then [] else linearSearchTrace x as)

#eval linearSearchTrace 9 [1, 3, 4, 5, 6, 8, 9, 11]
```

<details>
<summary>💡 답 보기</summary>

```
단계 1: 9와 1 비교 → 같지 않음 → 계속
단계 2: 9와 3 비교 → 같지 않음 → 계속
단계 3: 9와 4 비교 → 같지 않음 → 계속
단계 4: 9와 5 비교 → 같지 않음 → 계속
단계 5: 9와 6 비교 → 같지 않음 → 계속
단계 6: 9와 8 비교 → 같지 않음 → 계속
단계 7: 9와 9 비교 → 같다! → 위치 7에서 찾음
```

Lean4 출력: `[(1, false), (3, false), (4, false), (5, false), (6, false), (8, false), (9, true)]`

비교 횟수: **7번**

</details>

---

### 연습 8-2: Rosen 연습문제 13b — 이진 탐색으로 7 찾기

같은 수열에서 이진 탐색으로 7을 찾을 때의 모든 단계를 보여라. 7은 리스트에 없다.

<details>
<summary>💡 답 보기</summary>

리스트: [1, 3, 4, 5, 6, 8, 9, 11]

**1단계**: 전체 리스트 (8개), mid = 4번째 = 5
- 7 > 5 → 오른쪽 [6, 8, 9, 11]

**2단계**: [6, 8, 9, 11] (4개), mid = 2번째 = 9
- 7 < 9 → 왼쪽 [6, 8]

**3단계**: [6, 8] (2개), mid = 1번째 = 8
- 7 < 8 → 왼쪽 [6]

**4단계**: [6] (1개)
- 7 ≠ 6 → **못 찾음**

비교 횟수: **4번** (선형 탐색의 8번과 비교)

</details>

---

### 연습 8-3: 두 수의 최대공약수 (Rosen 연습문제 관련)

유클리드 호제법을 Lean4로 구현하라. 이것은 Rosen 교재 뒷부분에서 다루지만, 미리 연습해 보자.

힌트: gcd(a, 0) = a, gcd(a, b) = gcd(b, a % b) (b > 0일 때)

```lean
def myGcd : Nat → Nat → Nat
  | a, 0 => sorry
  | a, b + 1 => sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
def myGcd : Nat → Nat → Nat
  | a, 0     => a
  | a, b + 1 => myGcd (b + 1) (a % (b + 1))

#eval myGcd 12 8   -- 4
#eval myGcd 100 75  -- 25
#eval myGcd 7 3     -- 1
#eval myGcd 0 5     -- 5
```

**설명**:
- gcd(a, 0) = a (0으로 나누면 a 자체가 최대공약수)
- gcd(a, b) = gcd(b, a mod b) (유클리드 호제법)

Lean4에서 `b + 1` 패턴을 사용하는 이유는 `b`가 0이 아님을 명시적으로 표현하기 위해서이다. 이렇게 하면 Lean4의 종료 검사기가 "매번 두 번째 인수가 줄어든다"는 것을 쉽게 확인할 수 있다.

</details>

---

## 6B.11 **귀납법**(Induction)으로 알고리즘 증명하기 — 미리보기

### 왜 귀납법이 필요한가?

알고리즘의 정확성을 **완전히** 증명하려면, 모든 가능한 입력에 대해 알고리즘이 올바르게 동작한다는 것을 보여야 한다. 리스트의 길이가 무한히 클 수 있으므로, 유한한 개수의 예시로는 충분하지 않다.

**귀납법**(induction)은 이 문제를 해결한다. 핵심 아이디어:

1. **기저 사례**(base case): 가장 작은 입력(빈 리스트 또는 0)에 대해 올바름을 보인다
2. **귀납 단계**(inductive step): "크기 n인 입력에 대해 올바르다"고 가정하고, "크기 n+1인 입력에 대해서도 올바르다"를 보인다

이것은 **도미노**와 같다:
- 첫 번째 도미노를 쓰러뜨린다 (기저 사례)
- 어떤 도미노가 쓰러지면 다음 도미노도 쓰러진다 (귀납 단계)
- 따라서 모든 도미노가 쓰러진다 (모든 입력에 대해 올바르다)

### Lean4에서 귀납법 사용하기

```lean
-- myLength 함수가 올바르게 동작한다는 증명
-- "원소 하나를 앞에 붙이면 길이가 1 늘어난다"
theorem myLength_cons (a : Nat) (as : List Nat) :
  myLength (a :: as) = 1 + myLength as := by
  rfl  -- 정의에 의해 자명

-- 두 리스트를 이어붙인 것의 길이 = 각 길이의 합
theorem myLength_append (xs ys : List Nat) :
  myLength (xs ++ ys) = myLength xs + myLength ys := by
  induction xs with
  | nil =>
    -- 기저 사례: xs = []
    -- myLength ([] ++ ys) = myLength ys = 0 + myLength ys
    simp [myLength]
  | cons a as ih =>
    -- 귀납 단계: xs = a :: as
    -- 귀납 가정 ih : myLength (as ++ ys) = myLength as + myLength ys
    simp [myLength]
    rw [ih]
    omega
```

이 증명의 구조를 자세히 보자:

1. `induction xs with` — xs에 대한 귀납법을 시작한다
2. `| nil =>` — 기저 사례: xs가 빈 리스트인 경우
3. `| cons a as ih =>` — 귀납 단계: xs = a :: as인 경우. `ih`는 **귀납 가정**(inductive hypothesis)이다

**귀납 가정** `ih`는 "더 작은 리스트에 대해서는 성질이 성립한다"는 가정이다. 이것을 이용하여 "원래 리스트에 대해서도 성립한다"를 보인다.

---

## 6B.12 연습문제 세트 9: 증명 연습

### 연습 9-1: mySum의 기저 사례 (괄호 채우기)

```lean
theorem mySum_nil : mySum ([] : List Nat) = 0 := by
  (______)
```

<details>
<summary>💡 답 보기</summary>

```lean
theorem mySum_nil : mySum ([] : List Nat) = 0 := by
  rfl
```

**설명**: `mySum []`은 정의에 의해 `0`이므로 `rfl`로 충분하다.

</details>

---

### 연습 9-2: 정렬의 기본 성질

"빈 리스트는 정렬되어 있다"와 "원소 하나인 리스트는 정렬되어 있다"를 증명하라.

```lean
theorem sorted_nil : isSorted ([] : List Nat) = true := by
  sorry

theorem sorted_singleton (a : Nat) : isSorted [a] = true := by
  sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
theorem sorted_nil : isSorted ([] : List Nat) = true := by
  rfl

theorem sorted_singleton (a : Nat) : isSorted [a] = true := by
  rfl
```

**설명**: 둘 다 `isSorted`의 정의에 의해 `true`이므로 `rfl`로 충분하다.

</details>

---

### 연습 9-3: `insertionSort`의 기본 성질 (sorry 채우기)

```lean
-- 빈 리스트를 정렬하면 빈 리스트
theorem insertionSort_nil : insertionSort ([] : List Nat) = [] := by
  sorry

-- 원소 하나를 정렬하면 그대로
theorem insertionSort_singleton (a : Nat) : insertionSort [a] = [a] := by
  sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
theorem insertionSort_nil : insertionSort ([] : List Nat) = [] := by
  rfl

theorem insertionSort_singleton (a : Nat) : insertionSort [a] = [a] := by
  simp [insertionSort, insert]
```

**설명**:
- `insertionSort []`은 정의에 의해 `[]`이다
- `insertionSort [a] = insert a (insertionSort []) = insert a [] = [a]`

</details>

---

## 6B.13 전술 요약표 (Part 6-B까지)

### 이 파트에서 새로 배운 개념

| 개념 | Lean4 표현 | 설명 |
|------|-----------|------|
| `Array` | `#[1, 2, 3]` | 배열 — 인덱스 접근이 빠르다 |
| `where` | `def f := go where go ...` | 보조 함수를 같은 곳에 정의 |
| `termination_by` | `termination_by n` | 종료 증거 지정 |
| 귀납법 | `induction xs with ...` | 리스트/자연수에 대한 귀납적 증명 |
| `ih` | 귀납 가정 | "더 작은 경우에 성립"이라는 가정 |

### 알고리즘 요약

| 알고리즘 | 용도 | 시간 복잡도 | Lean4 함수 |
|-----------|------|-----------|-----------|
| 선형 탐색 | 리스트에서 값 찾기 | O(n) | `contains`, `linearSearch` |
| 이진 탐색 | 정렬된 리스트에서 값 찾기 | O(log n) | `binarySearch` |
| 버블 정렬 | 리스트 정렬 | O(n²) | `bubbleSort` |
| 삽입 정렬 | 리스트 정렬 | O(n²) | `insertionSort` |
| 문자열 매칭 | 패턴 찾기 | O(nm) | `findPattern` |
| 거스름돈 | 최소 동전 수 | O(r) | `makeChange` |

---

## 6B.14 도전 문제

### 도전 1: 선택 정렬(Selection Sort) 구현

**선택 정렬**은 리스트에서 가장 작은 원소를 찾아 맨 앞으로 이동하고, 나머지에 대해 반복하는 알고리즘이다.

```lean
-- 리스트에서 최솟값을 찾는 함수
def listMin : List Nat → Option Nat
  | []      => none
  | [a]     => some a
  | a :: as => match listMin as with
               | none   => some a
               | some m => some (if a ≤ m then a else m)

-- 리스트에서 특정 값의 첫 번째 출현을 제거
def removeFirst : Nat → List Nat → List Nat
  | _, []      => []
  | x, a :: as => if x == a then as else a :: removeFirst x as

-- 선택 정렬: sorry를 채워라
def selectionSort : List Nat → List Nat
  | [] => sorry
  | xs => sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
def selectionSort : List Nat → List Nat
  | [] => []
  | xs =>
    match listMin xs with
    | none   => []
    | some m => m :: selectionSort (removeFirst m xs)
termination_by xs.length

#eval selectionSort [3, 5, 4, 1, 2]  -- [1, 2, 3, 4, 5]
```

**설명**: 매번 최솟값을 찾아 결과의 앞에 놓고, 그 원소를 제거한 나머지에 대해 재귀한다. `termination_by xs.length`는 "매번 리스트 길이가 줄어들므로 종료한다"는 증거이다.

</details>

---

### 도전 2: 이진 탐색이 선형 탐색과 같은 결과를 내는지 확인

정렬된 리스트에서 이진 탐색과 선형 탐색이 같은 결과(있음/없음)를 내는지 몇 가지 예시로 확인하라.

```lean
-- 두 알고리즘의 결과가 같은지 확인하는 함수
def searchAgree (x : Nat) (xs : List Nat) : Bool :=
  contains x xs == sortedContains x xs

-- 여러 테스트 케이스
#eval searchAgree 5 [1, 2, 3, 4, 5]    -- true
#eval searchAgree 0 [1, 2, 3, 4, 5]    -- true
#eval searchAgree 3 []                   -- true
#eval searchAgree 7 [1, 3, 5, 7, 9]    -- true
```

물론 이 예시들이 "항상 같다"는 것을 **증명**하지는 않는다. 완전한 증명은 귀납법이 필요하며, 이는 향후 파트에서 다룬다.

---

### 도전 3: 두 수의 차의 최댓값 (Rosen 연습문제 20)

"정수의 유한한 길이의 리스트에서 가장 큰 값과 가장 작은 값을 **동시에** 찾는 알고리즘을 설명하라."

```lean
-- 리스트에서 최댓값과 최솟값을 동시에 찾기
-- 반환: (최솟값, 최댓값)
def findMinMax : List Nat → Option (Nat × Nat)
  | []      => sorry
  | [a]     => sorry
  | a :: as => sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
def findMinMax : List Nat → Option (Nat × Nat)
  | []      => none
  | [a]     => some (a, a)
  | a :: as =>
    match findMinMax as with
    | none          => some (a, a)
    | some (mn, mx) => some (min a mn, max a mx)

#eval findMinMax [3, 1, 4, 1, 5, 9, 2, 6]  -- some (1, 9)
#eval findMinMax [42]                        -- some (42, 42)
#eval findMinMax []                           -- none
```

**설명**: 나머지 리스트의 최솟값과 최댓값을 재귀적으로 구한 다음, 첫 원소와 비교하여 갱신한다. 이렇게 하면 리스트를 **한 번만** 훑으면서 최솟값과 최댓값을 동시에 찾을 수 있다.

</details>

---

## 6B.15 이 파트의 핵심 정리

1. **알고리즘 = Lean4 함수**: Rosen 교재의 의사 코드는 Lean4의 함수 정의로 정확히 번역된다
2. **재귀 = 루프**: 교재의 `for`/`while` 루프는 Lean4에서 **재귀**로 표현된다
3. **`#eval` = 추적(trace)**: 교재에서 알고리즘을 수동으로 추적하는 것은 `#eval`로 대체된다
4. **`theorem` = 정확성 증명**: 알고리즘이 올바르게 동작한다는 것을 수학적으로 증명할 수 있다
5. **종료 검사기**: Lean4는 함수가 반드시 종료한다는 것을 자동으로 확인한다
6. **정지 문제**: 모든 프로그램의 종료 여부를 판단하는 일반적인 방법은 존재하지 않는다

---

**(Part 6-B 끝)**

다음 파트(Part 7)에서는 **함수의 증가**(Growth of Functions)와 **알고리즘 복잡도**(Algorithm Complexity)를 학습하여, big-O 표기법과 알고리즘의 효율성을 Lean4로 분석하는 방법을 배운다.
