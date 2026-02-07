# Lean4 완전 정복 가이드 — 제8-G편

## **재귀 알고리즘 심화**(Advanced Recursive Algorithms) — 반복과 비교, 합병 정렬, 정확성 증명

> **교재**: Kenneth H. Rosen, *Discrete Mathematics and Its Applications* 8판 5.4절  
> **참고**: 『Mathematics in Lean』 Chapter 5.4 More Induction, Chapter 6.3 Inductively Defined Types  
> **선수 학습**: 제8-F편(재귀 알고리즘 기초: 팩토리얼, 거듭제곱, gcd, 이진 탐색)

---

## 8G.0 이 장의 목표

이 장에서 다루는 핵심 내용은 다음과 같다:

1. **재귀적 멱승의 나머지**(recursive modular exponentiation) — `bⁿ mod m`을 효율적으로 계산하기
2. **재귀와 반복의 비교**(recursion vs iteration) — 피보나치 수의 재귀/반복 구현
3. **합병 정렬**(merge sort) — 분할정복의 대표적 재귀 알고리즘
4. **재귀 알고리즘의 정확성 증명**(correctness proofs) — 수학적 귀납법으로 재귀 알고리즘이 옳다는 것을 증명하기
5. Lean4에서 이 모든 것을 직접 구현하고 검증하기

---

## 8G.1 **재귀적 멱승의 나머지**(Recursive Modular Exponentiation)

### 왜 필요한가?

암호학에서 가장 핵심적인 연산 중 하나가 `bⁿ mod m`의 계산이다. 예를 들어 RSA 암호에서는 매우 큰 수의 거듭제곱을 모듈러 연산으로 계산해야 한다.

직접 `bⁿ`을 먼저 계산한 다음 `mod m`을 하면? 숫자가 너무 커져서 컴퓨터가 감당할 수 없다! 예를 들어 `2¹⁰⁰⁰`은 약 300자리 수이다.

### 기본 아이디어: 중간에 나머지를 계속 취하기

**핵심 성질**: `(a · b) mod m = ((a mod m) · (b mod m)) mod m`

이 성질 덕분에, 큰 수를 직접 계산하지 않고도 나머지만으로 연산할 수 있다.

### 알고리즘 4 — 재귀적 멱승의 나머지 (교재)

교재의 의사코드를 살펴보자:

```
procedure mpower(b, n, m: 정수, b > 0, m ≥ 2, n ≥ 0)
if n = 0 then
    return 1
else if n이 짝수이면
    return mpower(b, n/2, m)² mod m
else
    return (mpower(b, ⌊n/2⌋, m)² mod m · b mod m) mod m
{output is bⁿ mod m}
```

이 알고리즘의 핵심 아이디어는 **반복 제곱법**(repeated squaring)이다:

- n이 짝수: `bⁿ = (b^(n/2))²`
- n이 홀수: `bⁿ = (b^(⌊n/2⌋))² · b`

매번 지수가 절반으로 줄어드므로, 총 약 `log₂ n`번의 곱셈만 필요하다!

### 교재 예제 4: `2⁵ mod 3` 추적

`b = 2, n = 5, m = 3`을 대입하여 알고리즘 4를 추적해 보자.

1. `n = 5`는 홀수 → else절로 간다
2. `mpower(2, 5, 3) = (mpower(2, 2, 3)² mod 3 · 2 mod 3) mod 3`
3. `mpower(2, 2, 3)`: n = 2는 짝수 → `mpower(2, 1, 3)² mod 3`
4. `mpower(2, 1, 3)`: n = 1은 홀수 → `(mpower(2, 0, 3)² mod 3 · 2 mod 3) mod 3`
5. `mpower(2, 0, 3) = 1` (기저 사례)

거꾸로 계산:
- `mpower(2, 0, 3) = 1`
- `mpower(2, 1, 3) = (1² mod 3 · 2 mod 3) mod 3 = (1 · 2) mod 3 = 2`
- `mpower(2, 2, 3) = 2² mod 3 = 4 mod 3 = 1`
- `mpower(2, 5, 3) = (1² mod 3 · 2 mod 3) mod 3 = (1 · 2) mod 3 = 2`

실제로 `2⁵ = 32`, `32 mod 3 = 2`. 정답이다! ✓

### Lean4 구현

```lean
def mpower : Nat → Nat → Nat → Nat
  | _, 0, _ => 1
  | b, n + 1, m =>
    if (n + 1) % 2 == 0 then
      -- n+1이 짝수
      let half := mpower b ((n + 1) / 2) m
      (half * half) % m
    else
      -- n+1이 홀수
      let half := mpower b ((n + 1) / 2) m
      (half * half % m * (b % m)) % m

-- 검증
#eval mpower 2 5 3     -- 2  (2⁵ = 32, 32 mod 3 = 2)
#eval mpower 2 10 3    -- 1  (2¹⁰ = 1024, 1024 mod 3 = 1)
#eval mpower 3 11 5    -- 3  (3¹¹ mod 5 = 3)
#eval mpower 7 10 2    -- 1  (7¹⁰ mod 2 = 1)
```

> **참고**: 이 함수는 Part 7-C에서 `modPow`라는 이름으로 이미 구현한 바 있다. 여기서는 교재의 의사코드와 더 가까운 형태로 다시 작성한 것이다.

### 연습: mpower 추적 (괄호 채우기)

`mpower(3, 4, 5)`를 추적하시오.

```
n = 4는 짝수
→ half = mpower(3, 2, 5)
  → n = 2는 짝수
  → half₂ = mpower(3, 1, 5)
    → n = 1은 홀수
    → half₃ = mpower(3, 0, 5) = (______)
    → (half₃² mod 5 · 3 mod 5) mod 5 = (______)
  → (half₂² mod 5) = (______)
→ (half² mod 5) = (______)
```

<details>
<summary>💡 답 보기</summary>

```
n = 4는 짝수
→ half = mpower(3, 2, 5)
  → n = 2는 짝수
  → half₂ = mpower(3, 1, 5)
    → n = 1은 홀수
    → half₃ = mpower(3, 0, 5) = 1
    → (1² mod 5 · 3 mod 5) mod 5 = (1 · 3) mod 5 = 3
  → (3² mod 5) = 9 mod 5 = 4
→ (4² mod 5) = 16 mod 5 = 1
```

검증: `3⁴ = 81`, `81 mod 5 = 1`. 정답! ✓

</details>

---

## 8G.2 **재귀적 선형 탐색**(Recursive Linear Search)

### 교재 알고리즘 5

교재에서는 선형 탐색을 재귀적으로 표현한다:

```
procedure search(i, j, x)
if aᵢ = x then
    return i
else if i = j then
    return 0
else
    return search(i + 1, j, x)
{output: aᵢ, ..., aⱼ에서 x의 위치, 없으면 0}
```

이 알고리즘의 아이디어는 간단하다:
- 첫 번째 원소가 x이면 → 위치를 반환
- 탐색 범위에 원소가 하나뿐인데 x가 아니면 → 못 찾음 (0 반환)
- 그 외 → 첫 번째 원소를 건너뛰고 나머지에서 재귀적으로 탐색

### Lean4 구현

```lean
-- 리스트 기반 재귀적 선형 탐색
-- 결과: 찾으면 Some (인덱스), 못 찾으면 None
def recLinearSearch (xs : List Nat) (x : Nat) (i : Nat := 0) : Option Nat :=
  match xs with
  | []      => none                          -- 빈 리스트 → 못 찾음
  | a :: as => if a == x then some i         -- 첫 원소가 x → 위치 반환
               else recLinearSearch as x (i + 1)  -- 나머지에서 계속 탐색

-- 검증
#eval recLinearSearch [1, 3, 5, 7, 9] 5    -- some 2
#eval recLinearSearch [1, 3, 5, 7, 9] 4    -- none
#eval recLinearSearch [2, 4, 6, 8] 8       -- some 3
#eval recLinearSearch [] 1                  -- none
```

### 교재와의 차이점

| 교재 | Lean4 |
|------|-------|
| 인덱스 1부터 시작 | 인덱스 0부터 시작 |
| 못 찾으면 0 반환 | 못 찾으면 `none` 반환 |
| 배열 기반 | 리스트 기반 (패턴 매칭 활용) |

Lean4에서 `Option` 타입을 사용하는 것이 더 안전하다. `0`을 반환하면 "인덱스 0에서 찾았다"와 "못 찾았다"를 구분할 수 없기 때문이다.

---

## 8G.3 **재귀적 이진 탐색**(Recursive Binary Search)

### 교재 알고리즘 6

```
procedure binary search(i, j, x)
m := ⌊(i + j) / 2⌋
if x = aₘ then
    return m
else if (x < aₘ and i < m) then
    return binary search(i, m - 1, x)
else if (x > aₘ and j > m) then
    return binary search(m + 1, j, x)
else return 0
{output: 정렬된 aᵢ, ..., aⱼ에서 x의 위치, 없으면 0}
```

### Lean4 구현

```lean
-- Array 기반 재귀적 이진 탐색
def recBinarySearch (arr : Array Nat) (x : Nat) (lo hi : Nat) : Option Nat :=
  if lo > hi then none
  else
    let mid := (lo + hi) / 2
    if h : mid < arr.size then
      let v := arr[mid]
      if x == v then some mid
      else if x < v then
        if mid == 0 then none
        else recBinarySearch arr x lo (mid - 1)
      else recBinarySearch arr x (mid + 1) hi
    else none
termination_by hi - lo + 1

-- 검증: 정렬된 배열에서 탐색
#eval recBinarySearch #[1, 3, 5, 7, 9, 11, 13] 7 0 6   -- some 3
#eval recBinarySearch #[1, 3, 5, 7, 9, 11, 13] 4 0 6   -- none
#eval recBinarySearch #[2, 4, 6, 8, 10] 2 0 4           -- some 0
#eval recBinarySearch #[2, 4, 6, 8, 10] 10 0 4          -- some 4
```

### 왜 이진 탐색이 효율적인가?

매번 탐색 범위가 **절반**으로 줄어든다:
- n개 원소 → n/2 → n/4 → ... → 1

따라서 최대 비교 횟수는 `⌈log₂ n⌉ + 1`이다.

예: 1,000,000개의 원소가 있을 때
- 선형 탐색: 최대 1,000,000번 비교
- 이진 탐색: 최대 21번 비교! (`log₂ 1000000 ≈ 20`)

---

## 8G.4 **재귀와 반복**(Recursion vs Iteration)

### 핵심 개념

**재귀적**(recursive) 정의란 함수의 값을 더 작은 정수에서의 함수값으로 표현하는 것이다. 이 정의를 그대로 코드로 옮기면 재귀 프로그램이 된다.

**반복적**(iterative) 접근법은 재귀를 사용하지 않고, 루프를 돌면서 값을 갱신하는 방식이다.

둘의 관계를 피보나치 수로 비교해 보자.

### 피보나치 수의 재귀적 계산 (교재 알고리즘 7)

```lean
-- 재귀적 피보나치 (Mathematics in Lean 스타일)
def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

-- 검증
#eval (List.range 10).map fib  -- [0, 1, 1, 2, 3, 5, 8, 13, 21, 34]
```

이 정의는 수학적으로 깔끔하지만, **계산적으로는 매우 비효율적**이다!

### 왜 비효율적인가? — 중복 계산의 폭발

`fib 4`를 계산하려면:
```
fib 4 = fib 2 + fib 3
      = (fib 0 + fib 1) + (fib 1 + fib 2)
      = (fib 0 + fib 1) + (fib 1 + (fib 0 + fib 1))
```

`fib 2`가 2번, `fib 1`이 3번, `fib 0`이 2번 계산된다!

교재 그림 1의 트리에서 볼 수 있듯이, `fib n`을 계산하는 데 필요한 덧셈 횟수는 약 `fib(n+1) - 1`번이며, 이는 **지수적으로 증가**한다. `fib n ≈ φⁿ/√5` (φ = (1 + √5)/2 ≈ 1.618)이므로, 계산 시간이 `O(1.618ⁿ)`이다.

### 피보나치 수의 반복적 계산 (교재 알고리즘 8)

```lean
-- 반복적 피보나치 (꼬리 재귀)
def fibIter (n : Nat) : Nat :=
  go n 0 1
where
  go : Nat → Nat → Nat → Nat
  | 0, x, _ => x
  | n + 1, x, y => go n y (x + y)

-- 검증
#eval (List.range 10).map fibIter  -- [0, 1, 1, 2, 3, 5, 8, 13, 21, 34]
```

이 버전은 **반복**을 사용한다. `x`와 `y`가 각각 연속된 두 피보나치 수를 추적하며, 매 단계에서 `(x, y) → (y, x + y)`로 갱신한다. 총 `n - 1`번의 덧셈만 필요하므로 **O(n)**이다!

### 성능 비교

```lean
-- 재귀 버전은 n = 35 정도만 돼도 느려진다
-- #eval fib 35   -- 수 초 이상 소요될 수 있음

-- 반복 버전은 매우 빠르다
#eval fibIter 100  -- 순식간에 계산
-- 354224848179261915075
```

### Mathematics in Lean의 꼬리 재귀 피보나치

Mathematics in Lean에서도 동일한 아이디어를 `fib'`이라는 이름으로 제시한다:

```lean
-- Mathematics in Lean 스타일
def fib' (n : Nat) : Nat :=
  aux n 0 1
where aux
  | 0, x, _ => x
  | n+1, x, y => aux n y (x + y)
```

그리고 두 구현이 같은 함수임을 증명한다:

```lean
-- 보조 정리: aux가 fib와 같은 값을 계산한다
theorem fib'.aux_eq (m n : Nat) :
    fib'.aux n (fib m) (fib (m + 1)) = fib (n + m) := by
  induction n generalizing m with
  | zero => simp [fib'.aux]
  | succ n ih => rw [fib'.aux, ←fib_add_two, ih, add_assoc, add_comm 1]

-- 메인 정리: fib' = fib
theorem fib'_eq_fib : fib' = fib := by
  ext n
  erw [fib', fib'.aux_eq 0 n]; rfl
```

> **`generalizing` 키워드**: `induction n generalizing m`은 귀납 가정에서 `m`을 전칭 한정(`∀ m`)으로 만든다. 이렇게 해야 귀납 단계에서 `m`에 `m + 1`을 대입할 수 있다.

### 재귀 vs 반복 — 정리

| 특성 | 재귀(Recursive) | 반복(Iterative) |
|------|----------------|----------------|
| 코드 가독성 | 수학 정의와 직접 대응 | 루프/상태 갱신으로 표현 |
| 효율성 | 중복 계산 가능 (지수적) | 보통 선형 또는 그 이하 |
| 증명 용이성 | 구조적으로 증명 가능 | 루프 불변값 필요 |
| 메모리 | 호출 스택 사용 | 상수 공간 가능 |
| Lean4 스타일 | `def fib | 0 => ...` | `where go | ...` |

---

## 8G.5 연습문제 세트 1: 재귀 구현

### 연습 1-1: `n!` 재귀적 계산 (괄호 채우기)

```lean
def myFactorial : Nat → Nat
  | 0 => (______)
  | n + 1 => (______) * myFactorial (______)

#eval myFactorial 5  -- 120이 나와야 함
```

<details>
<summary>💡 답 보기</summary>

```lean
def myFactorial : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * myFactorial n

#eval myFactorial 5  -- 120
```

**설명**: `0! = 1`이고, `(n+1)! = (n+1) × n!`이다.

</details>

---

### 연습 1-2: `n!`의 반복적 계산 (sorry 채우기)

```lean
def myFactIter (n : Nat) : Nat :=
  go n 1
where
  go : Nat → Nat → Nat
  | 0, acc => sorry
  | k + 1, acc => sorry

#eval myFactIter 5  -- 120이 나와야 함
```

<details>
<summary>💡 답 보기</summary>

```lean
def myFactIter (n : Nat) : Nat :=
  go n 1
where
  go : Nat → Nat → Nat
  | 0, acc => acc
  | k + 1, acc => go k (acc * (k + 1))

#eval myFactIter 5  -- 120
```

**설명**: `acc`(누적기)에 값을 곱해 나간다. `go 5 1 → go 4 5 → go 3 20 → go 2 60 → go 1 120 → go 0 120 → 120`.

</details>

---

### 연습 1-3: mpower 추적 (Rosen 연습문제 5)

`m = 5, n = 11, b = 3`일 때 `mpower(3, 11, 5)`를 추적하여 `3¹¹ mod 5`를 계산하시오.

<details>
<summary>💡 답 보기</summary>

```
mpower(3, 11, 5): n=11 홀수
  → half = mpower(3, 5, 5)
    mpower(3, 5, 5): n=5 홀수
      → half = mpower(3, 2, 5)
        mpower(3, 2, 5): n=2 짝수
          → half = mpower(3, 1, 5)
            mpower(3, 1, 5): n=1 홀수
              → half = mpower(3, 0, 5) = 1
              → (1² mod 5 · 3 mod 5) mod 5 = 3
          → (3² mod 5) = 9 mod 5 = 4
      → (4² mod 5 · 3 mod 5) mod 5 = (16 mod 5 · 3) mod 5 = (1 · 3) mod 5 = 3
  → (3² mod 5 · 3 mod 5) mod 5 = (9 mod 5 · 3) mod 5 = (4 · 3) mod 5 = 12 mod 5 = 2
```

검증: `3¹¹ = 177147`, `177147 mod 5 = 2`. ✓

```lean
#eval mpower 3 11 5      -- 2
#eval 3 ^ 11 % 5         -- 2
```

</details>

---

### 연습 1-4: `bⁿ mod m`의 단순 재귀 (Rosen 연습문제 12)

`xⁿ mod m`을 `xⁿ mod m = (xⁿ⁻¹ mod m · x mod m) mod m`을 기반으로 구하는 재귀 알고리즘을 작성하시오. 이것은 효율적인 mpower와 달리 O(n)이다.

```lean
def simpleMPower : Nat → Nat → Nat → Nat
  | _, 0, _ => sorry
  | b, n + 1, m => sorry

#eval simpleMPower 2 10 3  -- 1이 나와야 함
```

<details>
<summary>💡 답 보기</summary>

```lean
def simpleMPower : Nat → Nat → Nat → Nat
  | _, 0, _ => 1
  | b, n + 1, m => (simpleMPower b n m * (b % m)) % m

#eval simpleMPower 2 10 3  -- 1
#eval simpleMPower 3 11 5  -- 2
```

**설명**: `bⁿ mod m = (bⁿ⁻¹ mod m · b mod m) mod m`. 단순하지만 O(n) — mpower의 O(log n)보다 느리다.

</details>

---

## 8G.6 **합병 정렬**(Merge Sort) — 분할정복의 정수

### 합병 정렬이란?

**합병 정렬**(merge sort)은 다음의 세 단계로 동작하는 정렬 알고리즘이다:

1. **분할**(divide): 리스트를 두 개의 부분 리스트로 나눈다
2. **정복**(conquer): 각 부분 리스트를 재귀적으로 정렬한다
3. **합병**(merge): 정렬된 두 부분 리스트를 하나의 정렬된 리스트로 합친다

이 과정은 부분 리스트의 원소가 하나가 될 때까지 반복된다 (원소 하나인 리스트는 이미 정렬됨).

### 교재 예제 9: `[8, 2, 4, 6, 9, 7, 10, 1, 5, 3]`의 합병 정렬

교재의 그림 2를 따라가 보자:

**분할 단계** (위에서 아래로):
```
[8, 2, 4, 6, 9, 7, 10, 1, 5, 3]
          ↓
[8, 2, 4, 6, 9]    [7, 10, 1, 5, 3]
     ↓                    ↓
[8, 2, 4]  [6, 9]  [7, 10, 1]  [5, 3]
   ↓         ↓        ↓          ↓
[8, 2] [4] [6] [9] [7, 10] [1] [5] [3]
  ↓                   ↓
[8] [2]             [7] [10]
```

**합병 단계** (아래에서 위로):
```
[8] [2] → [2, 8]       [7] [10] → [7, 10]
[2, 8] [4] → [2, 4, 8]   [7, 10] [1] → [1, 7, 10]
[6] [9] → [6, 9]         [5] [3] → [3, 5]
[2, 4, 8] [6, 9] → [2, 4, 6, 8, 9]    [1, 7, 10] [3, 5] → [1, 3, 5, 7, 10]
        [2, 4, 6, 8, 9] [1, 3, 5, 7, 10] → [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
```

### Lean4 구현 — merge 함수

먼저 두 개의 정렬된 리스트를 합병하는 함수를 만들자:

```lean
-- 두 정렬된 리스트를 하나의 정렬된 리스트로 합병
def merge : List Nat → List Nat → List Nat
  | [], bs => bs
  | as, [] => as
  | a :: as, b :: bs =>
    if a ≤ b then a :: merge as (b :: bs)
    else b :: merge (a :: as) bs
termination_by xs ys => xs.length + ys.length

-- 검증
#eval merge [2, 3, 5, 6] [1, 4]
-- [1, 2, 3, 4, 5, 6]
```

### 교재 예제 10: `[2, 3, 5, 6]`과 `[1, 4]`의 합병

교재의 표 1을 따라가 보자:

| 단계 | 첫 번째 리스트 | 두 번째 리스트 | 합병된 리스트 | 비교 |
|------|------------|------------|-----------|------|
| 1 | [2, 3, 5, 6] | [1, 4] | [] | 1 < 2 |
| 2 | [2, 3, 5, 6] | [4] | [1] | 2 < 4 |
| 3 | [3, 5, 6] | [4] | [1, 2] | 3 < 4 |
| 4 | [5, 6] | [4] | [1, 2, 3] | 4 < 5 |
| 5 | [5, 6] | [] | [1, 2, 3, 4] | — |
| 6 | — | — | [1, 2, 3, 4, 5, 6] | — |

비교 횟수: 4번. (교재 보조정리 1: m + n - 1 = 4 + 2 - 1 = 5 이하)

### Lean4 구현 — mergeSort 함수

```lean
-- 리스트를 반으로 나누기
def splitList : List Nat → List Nat × List Nat
  | [] => ([], [])
  | [a] => ([a], [])
  | a :: b :: rest =>
    let (l, r) := splitList rest
    (a :: l, b :: r)

-- 합병 정렬
def mergeSort : List Nat → List Nat
  | [] => []
  | [a] => [a]
  | a :: b :: rest =>
    let (l, r) := splitList (a :: b :: rest)
    merge (mergeSort l) (mergeSort r)
termination_by xs => xs.length

-- 검증
#eval mergeSort [8, 2, 4, 6, 9, 7, 10, 1, 5, 3]
-- [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

#eval mergeSort [5, 3, 1, 4, 2]
-- [1, 2, 3, 4, 5]

#eval mergeSort [1]    -- [1]
#eval mergeSort []     -- []
```

### 합병 정렬의 시간 복잡도

**교재 정리 1**: n개의 원소를 갖는 리스트를 합병 정렬하는 데 필요한 비교 수는 **O(n log n)**이다.

이것은 버블 정렬의 O(n²)보다 훨씬 좋다:

| n | 버블 정렬 (n²) | 합병 정렬 (n log n) | 비율 |
|---|------------|---------------|------|
| 100 | 10,000 | 664 | 15배 |
| 1,000 | 1,000,000 | 9,966 | 100배 |
| 1,000,000 | 10¹² | 19,931,569 | 50,000배 |

합병 정렬은 **비교에 의한 정렬 중 최선의 big-O 척도**를 가진다 (교재).

---

## 8G.7 연습문제 세트 2: 합병 정렬

### 연습 2-1: 합병 추적 (Rosen 연습문제 46a)

리스트 쌍 `[1, 3, 5, 7, 9]`와 `[2, 4, 6, 8, 10]`을 합병하는 데 필요한 비교 수를 구하시오.

<details>
<summary>💡 답 보기</summary>

| 단계 | 리스트 1 | 리스트 2 | 합병 결과 | 비교 |
|------|--------|--------|---------|------|
| 1 | [1,3,5,7,9] | [2,4,6,8,10] | [] | 1 < 2 |
| 2 | [3,5,7,9] | [2,4,6,8,10] | [1] | 2 < 3 |
| 3 | [3,5,7,9] | [4,6,8,10] | [1,2] | 3 < 4 |
| 4 | [5,7,9] | [4,6,8,10] | [1,2,3] | 4 < 5 |
| 5 | [5,7,9] | [6,8,10] | [1,2,3,4] | 5 < 6 |
| 6 | [7,9] | [6,8,10] | [1,2,3,4,5] | 6 < 7 |
| 7 | [7,9] | [8,10] | [1,2,3,4,5,6] | 7 < 8 |
| 8 | [9] | [8,10] | [1,2,3,4,5,6,7] | 8 < 9 |
| 9 | [9] | [10] | [1,2,3,4,5,6,7,8] | 9 < 10 |

비교 수: **9번** (= m + n - 1 = 5 + 5 - 1)

이 경우 비교 수가 최대(보조정리 1의 상한)이다. 교대로 원소가 선택되기 때문이다.

```lean
#eval merge [1, 3, 5, 7, 9] [2, 4, 6, 8, 10]
-- [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
```

</details>

---

### 연습 2-2: 합병 정렬 실행 (Rosen 연습문제 44)

`[4, 3, 2, 5, 1, 8, 7, 6]`을 합병 정렬로 정렬하되, 각 단계를 보이시오.

<details>
<summary>💡 답 보기</summary>

**분할**:
```
[4, 3, 2, 5, 1, 8, 7, 6]
[4, 3, 2, 5] | [1, 8, 7, 6]
[4, 3] | [2, 5] | [1, 8] | [7, 6]
[4] | [3] | [2] | [5] | [1] | [8] | [7] | [6]
```

**합병**:
```
[3, 4] | [2, 5] | [1, 8] | [6, 7]
[2, 3, 4, 5] | [1, 6, 7, 8]
[1, 2, 3, 4, 5, 6, 7, 8]
```

```lean
#eval mergeSort [4, 3, 2, 5, 1, 8, 7, 6]
-- [1, 2, 3, 4, 5, 6, 7, 8]
```

</details>

---

### 연습 2-3: merge 함수 구현 (sorry 채우기)

```lean
def myMerge : List Nat → List Nat → List Nat
  | [], bs => sorry
  | as, [] => sorry
  | a :: as, b :: bs =>
    if a ≤ b then sorry
    else sorry

#eval myMerge [1, 3, 5] [2, 4, 6]  -- [1, 2, 3, 4, 5, 6]이 나와야 함
```

<details>
<summary>💡 답 보기</summary>

```lean
def myMerge : List Nat → List Nat → List Nat
  | [], bs => bs
  | as, [] => as
  | a :: as, b :: bs =>
    if a ≤ b then a :: myMerge as (b :: bs)
    else b :: myMerge (a :: as) bs
termination_by xs ys => xs.length + ys.length

#eval myMerge [1, 3, 5] [2, 4, 6]  -- [1, 2, 3, 4, 5, 6]
```

</details>

---

## 8G.8 **재귀 알고리즘의 정확성 증명**(Proving Correctness of Recursive Algorithms)

### 핵심 원리

수학적 귀납법과 강 귀납법은 재귀적 알고리즘이 올바른지(즉, 모든 가능한 입력에 대하여 원하는 결과를 만든다는 것을) 증명하는 데 이용될 수 있다.

### 교재 예제 7: `power(a, n)` 알고리즘의 정확성

`a ≠ 0`인 실수이고, `n`은 음이 아닌 정수일 때, 알고리즘 2(`power`)가 `aⁿ`을 맞게 계산하는지 증명하자.

**증명**: 지수 `n`에 대한 귀납법을 쓴다.

**기본 단계**: `n = 0`이면 알고리즘은 `power(a, 0) = 1`을 준다. `a⁰ = 1`이므로 맞다. ✓

**귀납적 단계**: 모든 `a ≠ 0`과 모든 음이 아닌 정수 `k`에 대해 `power(a, k) = aᵏ`이라고 가정하자 (귀납 가설). 이 가정이 `k + 1`에서도 성립함을 보여야 한다.

`k + 1 ≥ 1`이므로 알고리즘은 `a · power(a, k)`를 계산한다. 귀납 가설에 의해 `power(a, k) = aᵏ`이므로:

`power(a, k + 1) = a · power(a, k) = a · aᵏ = aᵏ⁺¹` ✓

### Lean4에서의 증명

```lean
-- 재귀적 거듭제곱 정의
def power (a : Nat) : Nat → Nat
  | 0 => 1
  | n + 1 => a * power a n

-- power가 a^n과 같음을 귀납법으로 증명
theorem power_eq_pow (a n : Nat) : power a n = a ^ n := by
  induction n with
  | zero =>
    -- 기본 단계: power a 0 = 1 = a ^ 0
    simp [power]
  | succ n ih =>
    -- 귀납 단계: power a (n+1) = a * power a n = a * a^n = a^(n+1)
    simp [power, pow_succ, ih]

-- 구체적 검증
example : power 2 10 = 1024 := by native_decide
example : power 3 5 = 243 := by native_decide
```

### 교재 예제 8: `mpower(b, n, m)` 알고리즘의 정확성

이 증명은 **강 귀납법**을 사용한다. 지수 `n`에 대한 강 귀납법을 쓴다.

**기본 단계**: `n = 0`이면, `mpower(b, 0, m) = 1`이고, `b⁰ mod m = 1 mod m = 1`. ✓

**귀납적 단계**: 모든 `0 ≤ j < k`에 대해 `mpower(b, j, m) = bʲ mod m`이라 가정하자.

- `k`가 짝수이면: `mpower(b, k, m) = (mpower(b, k/2, m))² mod m`

  귀납 가설에 의해 `mpower(b, k/2, m) = b^(k/2) mod m`이므로:
  
  `= (b^(k/2) mod m)² mod m = (b^(k/2))² mod m = bᵏ mod m` ✓

- `k`가 홀수이면: `mpower(b, k, m) = ((mpower(b, ⌊k/2⌋, m))² mod m · b mod m) mod m`

  귀납 가설에 의해 `mpower(b, ⌊k/2⌋, m) = b^(⌊k/2⌋) mod m`이므로:
  
  `= (b^(⌊k/2⌋))² · b) mod m = b^(2⌊k/2⌋+1) mod m = bᵏ mod m` ✓

  (왜냐하면 `k`가 홀수이면 `2⌊k/2⌋ + 1 = k`이므로)

### Lean4에서의 간단한 확인

완전한 형식적 증명은 복잡하지만, 구체적인 값으로 확인할 수 있다:

```lean
-- mpower가 올바른 결과를 주는지 확인
example : mpower 2 10 3 = 2 ^ 10 % 3 := by native_decide
example : mpower 3 7 5 = 3 ^ 7 % 5 := by native_decide
example : mpower 7 13 11 = 7 ^ 13 % 11 := by native_decide
```

---

## 8G.9 연습문제 세트 3: 정확성 증명

### 연습 3-1: `power` 정확성의 기본 단계 (괄호 채우기)

```lean
-- power a 0 = a ^ 0임을 증명
theorem power_base (a : Nat) : power a 0 = a ^ 0 := by
  simp [(______)]
```

<details>
<summary>💡 답 보기</summary>

```lean
theorem power_base (a : Nat) : power a 0 = a ^ 0 := by
  simp [power]
```

**설명**: `power a 0 = 1`이고 `a ^ 0 = 1`이므로, `power`의 정의를 펼치면 `simp`가 해결한다.

</details>

---

### 연습 3-2: `myFactorial`의 정확성 (sorry 채우기)

```lean
-- myFactorial이 Nat.factorial과 같음을 증명
theorem myFact_eq (n : Nat) : myFactorial n = Nat.factorial n := by
  induction n with
  | zero => sorry
  | succ n ih => sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
theorem myFact_eq (n : Nat) : myFactorial n = Nat.factorial n := by
  induction n with
  | zero => simp [myFactorial, Nat.factorial]
  | succ n ih =>
    simp [myFactorial, Nat.factorial, ih]
```

**설명**: 기본 단계에서 `myFactorial 0 = 1 = Nat.factorial 0`이고, 귀납 단계에서 `myFactorial (n+1) = (n+1) * myFactorial n = (n+1) * Nat.factorial n = Nat.factorial (n+1)`.

</details>

---

### 연습 3-3: 재귀적 gcd의 정확성 (Rosen 연습문제 19)

`a < b`인 양의 정수에 대해, 재귀 알고리즘 3 (`gcd(a,b) = gcd(b mod a, a)`)이 올바름을 `#eval`로 확인하시오.

```lean
-- 재귀 gcd
def myGcd : Nat → Nat → Nat
  | 0, b => b
  | a + 1, b => myGcd (b % (a + 1)) (a + 1)

-- 여러 쌍에 대해 Lean4 내장 gcd와 같은 결과가 나오는지 확인
#eval (myGcd 5 8, Nat.gcd 5 8)       -- 같은 값?
#eval (myGcd 12 18, Nat.gcd 12 18)   -- 같은 값?
#eval (myGcd 100 75, Nat.gcd 100 75) -- 같은 값?
```

<details>
<summary>💡 답 보기</summary>

```lean
#eval (myGcd 5 8, Nat.gcd 5 8)       -- (1, 1) ✓
#eval (myGcd 12 18, Nat.gcd 12 18)   -- (6, 6) ✓
#eval (myGcd 100 75, Nat.gcd 100 75) -- (25, 25) ✓
```

모든 경우에 내장 `Nat.gcd`와 같은 결과를 준다.

</details>

---

### 연습 3-4: 피보나치 연속항의 서로소 (도전)

Mathematics in Lean에서 증명된 정리: 연속된 피보나치 수는 서로소이다.

```lean
-- fib_coprime_fib_succ의 구조를 따라가 보자
-- 힌트: fib (n + 2) = fib n + fib (n + 1)이므로
-- gcd(fib n, fib (n+1)) = gcd(fib n, fib n + fib (n-1)) = gcd(fib n, fib (n-1))

-- 구체적 확인
#eval Nat.gcd (fib 10) (fib 11)  -- 무엇이 나올까?
#eval Nat.gcd (fib 20) (fib 21)  -- 무엇이 나올까?
```

<details>
<summary>💡 답 보기</summary>

```lean
#eval Nat.gcd (fib 10) (fib 11)  -- 1
#eval Nat.gcd (fib 20) (fib 21)  -- 1
```

연속된 피보나치 수는 항상 서로소이다! Mathematics in Lean의 증명:

```lean
theorem fib_coprime_fib_succ (n : Nat) :
    Nat.Coprime (fib n) (fib (n + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [fib, Nat.coprime_add_self_right]
    exact ih.symm
```

이 증명의 핵심: `fib (n+2) = fib n + fib (n+1)`이므로, `gcd(fib (n+1), fib (n+2)) = gcd(fib (n+1), fib n + fib (n+1)) = gcd(fib (n+1), fib n) = gcd(fib n, fib (n+1))`. 귀납 가설에 의해 이것이 1이다.

</details>

---

## 8G.10 **교재 연습문제 풀이**(5.4절)

### 연습문제 1: 알고리즘 1 추적 (n = 5)

`n = 5`를 대입하여 알고리즘 1(팩토리얼 재귀)을 추적하시오.

<details>
<summary>💡 답 보기</summary>

알고리즘 1: `factorial(n) = if n = 0 then 1 else n * factorial(n-1)`

```
factorial(5) = 5 * factorial(4)
             = 5 * (4 * factorial(3))
             = 5 * (4 * (3 * factorial(2)))
             = 5 * (4 * (3 * (2 * factorial(1))))
             = 5 * (4 * (3 * (2 * (1 * factorial(0)))))
             = 5 * (4 * (3 * (2 * (1 * 1))))
             = 5 * (4 * (3 * (2 * 1)))
             = 5 * (4 * (3 * 2))
             = 5 * (4 * 6)
             = 5 * 24
             = 120
```

```lean
#eval myFactorial 5  -- 120
```

</details>

---

### 연습문제 7: nx를 덧셈만으로 계산하는 재귀 알고리즘 (Rosen 연습문제 7)

```lean
-- nx를 덧셈만으로 재귀적으로 계산
def mulByAdd : Nat → Nat → Nat
  | 0, _ => sorry
  | n + 1, x => sorry

#eval mulByAdd 5 7  -- 35가 나와야 함
```

<details>
<summary>💡 답 보기</summary>

```lean
def mulByAdd : Nat → Nat → Nat
  | 0, _ => 0
  | n + 1, x => x + mulByAdd n x

#eval mulByAdd 5 7  -- 35
#eval mulByAdd 0 10 -- 0
#eval mulByAdd 3 4  -- 12
```

**설명**: `n × x = x + (n-1) × x`. 기저 사례: `0 × x = 0`.

</details>

---

### 연습문제 8: 처음 n개의 양의 정수의 합 (Rosen 연습문제 8)

```lean
def sumFirst : Nat → Nat
  | 0 => sorry
  | n + 1 => sorry

#eval sumFirst 10  -- 55가 나와야 함 (1+2+...+10)
```

<details>
<summary>💡 답 보기</summary>

```lean
def sumFirst : Nat → Nat
  | 0 => 0
  | n + 1 => (n + 1) + sumFirst n

#eval sumFirst 10  -- 55
#eval sumFirst 100 -- 5050
```

**설명**: `sum(n) = n + sum(n-1)`, `sum(0) = 0`.

</details>

---

### 연습문제 18: `n!`을 계산하는 알고리즘의 정확성 증명 (Rosen 연습문제 18)

알고리즘 1이 `n!`을 올바르게 계산함을 Lean4로 증명하시오.

```lean
-- 정확성: myFactorial n = n!
theorem myFact_correct : ∀ n, myFactorial n = Nat.factorial n := by
  intro n
  induction n with
  | zero => sorry
  | succ n ih => sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
theorem myFact_correct : ∀ n, myFactorial n = Nat.factorial n := by
  intro n
  induction n with
  | zero =>
    -- myFactorial 0 = 1 = Nat.factorial 0
    simp [myFactorial, Nat.factorial]
  | succ n ih =>
    -- myFactorial (n+1) = (n+1) * myFactorial n
    -- = (n+1) * Nat.factorial n  (귀납 가설)
    -- = Nat.factorial (n+1)
    simp [myFactorial, Nat.factorial, ih]
```

</details>

---

### 연습문제 23: `(n+1)² = n² + 2n + 1`을 이용한 재귀 (Rosen 연습문제 23)

```lean
-- n²을 (n+1)² = n² + 2n + 1로 재귀적으로 계산
def sqRec : Nat → Nat
  | 0 => sorry
  | n + 1 => sorry

-- 정확성 검증
#eval (List.range 10).map (fun n => (sqRec n, n * n))
```

<details>
<summary>💡 답 보기</summary>

```lean
def sqRec : Nat → Nat
  | 0 => 0
  | n + 1 => sqRec n + 2 * n + 1

#eval (List.range 10).map (fun n => (sqRec n, n * n))
-- [(0,0), (1,1), (4,4), (9,9), (16,16), (25,25), (36,36), (49,49), (64,64), (81,81)]
```

**설명**: `(n+1)² = n² + 2n + 1`. 곱셈을 사용하지 않고 덧셈만으로 제곱수를 계산한다!

**정확성 증명**:

```lean
theorem sqRec_eq (n : Nat) : sqRec n = n * n := by
  induction n with
  | zero => simp [sqRec]
  | succ n ih => simp [sqRec, ih]; ring
```

</details>

---

## 8G.11 **피보나치 수의 성질**(Properties of Fibonacci Numbers)

### Mathematics in Lean의 피보나치 정리들

Mathematics in Lean에서는 피보나치 수에 관한 여러 정리를 다룬다. 가장 인상적인 것은 **비네 공식**(Binet's formula)이다:

$$f_n = \frac{\varphi^n - \psi^n}{\sqrt{5}}$$

여기서 $\varphi = \frac{1 + \sqrt{5}}{2}$ (황금비), $\psi = \frac{1 - \sqrt{5}}{2}$ (그 켤레)이다.

이것은 자연수로 정의된 피보나치 수열이 실수(무리수!)로 표현된다는 놀라운 결과이다.

### 피보나치 덧셈 정리

```lean
-- fib (m + n + 1) = fib m * fib n + fib (m + 1) * fib (n + 1)
-- Mathematics in Lean에서 두 가지 증명이 제시된다

-- 방법 1: induction with generalizing
theorem fib_add (m n : Nat) :
    fib (m + n + 1) = fib m * fib n + fib (m + 1) * fib (n + 1) := by
  induction n generalizing m with
  | zero => simp
  | succ n ih =>
    specialize ih (m + 1)
    rw [add_assoc m 1 n, add_comm 1 n] at ih
    simp only [fib, Nat.succ_eq_add_one, ih]
    ring
```

### 연습: 피보나치 제곱합 (Mathematics in Lean 연습문제)

```lean
-- fib(n)² + fib(n+1)² = fib(2n+1)
-- 힌트: fib_add를 사용
example (n : Nat) : (fib n) ^ 2 + (fib (n + 1)) ^ 2 = fib (2 * n + 1) := by
  sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
example (n : Nat) : (fib n) ^ 2 + (fib (n + 1)) ^ 2 = fib (2 * n + 1) := by
  have h := fib_add n n
  rw [show n + n + 1 = 2 * n + 1 from by omega] at h
  rw [← h]
  ring
```

</details>

---

## 8G.12 전술 및 함수 종합 요약

### 이 편(8-G)에서 사용한 핵심 개념

| 개념 | 설명 |
|------|------|
| **반복 제곱법** | `bⁿ mod m`을 O(log n)에 계산 |
| **재귀 vs 반복** | 같은 함수의 두 구현 방식 |
| **꼬리 재귀** | 보조 함수 + 누적기 패턴 |
| **합병 정렬** | 분할정복 O(n log n) 정렬 |
| **정확성 증명** | 귀납법으로 재귀 알고리즘의 옳음 증명 |
| **`generalizing`** | 귀납 가설에 전칭 한정 추가 |

### Lean4 전술 요약

| 전술 | 용도 | 이 장의 예 |
|------|------|---------|
| `induction n with` | 자연수 귀납법 | power, factorial 정확성 |
| `simp [f]` | 재귀 정의 풀기 + 단순화 | `simp [power]` |
| `ring` | 대수적 등식 | `(n+1)² = n² + 2n + 1` |
| `omega` | 선형 산술 | `n + n + 1 = 2 * n + 1` |
| `native_decide` | 계산 검증 | `mpower 2 10 3 = ...` |
| `rfl` | 정의에 의한 동치 | 기저 사례 |
| `termination_by` | 종료 증거 | merge, mergeSort |

### Lean4 함수 요약

| 함수 | 의미 | 시간 복잡도 |
|------|------|-----------|
| `mpower b n m` | bⁿ mod m | O(log n) |
| `fibIter n` | n번째 피보나치 수 | O(n) |
| `merge l r` | 정렬된 리스트 합병 | O(m + n) |
| `mergeSort xs` | 합병 정렬 | O(n log n) |

---

## 8G.13 핵심 요약

1. **반복 제곱법**(`mpower`)은 `bⁿ mod m`을 O(log n)에 계산한다. 암호학의 핵심 연산이다.

2. **재귀 vs 반복**: 같은 함수라도 재귀 구현은 O(2ⁿ), 반복 구현은 O(n)이 될 수 있다 (피보나치). Lean4에서는 꼬리 재귀(`where go`)로 효율적 반복을 표현한다.

3. **합병 정렬**은 O(n log n) 정렬 알고리즘이며, 비교 기반 정렬 중 최선의 복잡도를 가진다.

4. **정확성 증명**: 재귀 알고리즘의 정확성은 수학적 귀납법으로 증명한다. 기본 단계에서 가장 작은 입력을 확인하고, 귀납 단계에서 재귀 호출의 결과를 귀납 가설로 대체한다.

5. Mathematics in Lean의 피보나치 정리들(서로소, 덧셈 정리, 꼬리 재귀 동치)은 재귀와 귀납법의 아름다운 응용이다.

---

## 다음 편 예고

다음 편(제8-H편)에서는:
- **프로그램 정확성**(program correctness)의 기본 개념
- **호어 트리플**(Hoare triple) `p{S}q`
- **합성 규칙**(composition rule), **조건문 규칙**, **루프 불변값**(loop invariant)
- Lean4에서 프로그램의 정확성을 형식적으로 증명하기

를 다룬다.

---

**(끝)**
