# Lean4 Tutorial Part 8-F: **재귀 알고리즘**(Recursive Algorithms)

> **기반 교재**: Kenneth H. Rosen, *Discrete Mathematics and Its Applications* 8판 5.4절  
> **참고 교재**: *Mathematics in Lean* Chapter 5.2, 5.4  
> **선수 지식**: Part 8-A~8-E (수학적 귀납법, 강 귀납법, 재귀적 정의, 구조적 귀납법)

---

## 8F.0 이 파트에서 배우는 것

5장의 마지막 파트이다! 지금까지 **귀납법**(증명)과 **재귀적 정의**(정의)를 배웠다. 이번에는 이 두 도구를 합쳐서 **재귀 알고리즘**(recursive algorithm)을 만들고, 그 **정확성**(correctness)을 증명하는 방법을 배운다.

이 파트에서 다루는 내용:

1. **재귀 알고리즘**이란 무엇인가
2. **팩토리얼** 재귀 알고리즘 (Rosen 예제 1)
3. **거듭제곱** 재귀 알고리즘 (Rosen 예제 2)
4. **최대공약수** 재귀 알고리즘 (Rosen 예제 3)
5. **이진 탐색** 재귀 알고리즘 (Rosen 예제 4)
6. **병합 정렬** 재귀 알고리즘 (Rosen 예제 5)
7. 재귀 알고리즘의 **정확성 증명**

> 💡 **핵심 통찰**:
>
> "재귀(recursion)를 이해하려면, 먼저 재귀(recursion)를 이해해야 한다."  
> — 유명한 컴퓨터 과학 격언
>
> | 개념 | 정의에서 | 증명에서 | 알고리즘에서 |
> |------|---------|---------|-----------|
> | 기본 단계 | f(0) = 값 | P(0) 참 | 입력이 최소일 때 직접 답 |
> | 재귀 단계 | f(n+1) = ...f(n)... | P(k)→P(k+1) | 작은 문제로 쪼개서 풀기 |

---

## 8F.1 재귀 알고리즘이란? (Rosen 정리 1)

### 정의

**재귀 알고리즘**(recursive algorithm)이란, 문제를 **보다 작은 입력**을 갖는 **동일한 문제**로 단순화시켜 해결하는 알고리즘이다.

> **Rosen 정리 1**: 어떤 알고리즘이 문제를 보다 작은 입력을 갖는 동일한 문제로 단순화시켜 해결한다면, 이 알고리즘은 **재귀적**이라 불린다.

### 재귀 알고리즘의 구조

모든 재귀 알고리즘은 다음 두 부분을 갖는다:

| 부분 | 이름 | 역할 | 없으면? |
|------|------|------|--------|
| ① | **기저 사례**(base case) | 가장 작은 입력에 대한 답을 직접 제공 | **무한 루프**! |
| ② | **재귀 호출**(recursive call) | 더 작은 입력으로 자기 자신을 호출 | 의미 없음 |

### 비유: 러시아 인형 (마트료시카)

재귀 알고리즘은 **마트료시카**(matryoshka) 인형과 비슷하다:

- 큰 인형을 열면 → 같은 모양의 작은 인형이 나온다 (재귀 호출)
- 가장 작은 인형은 더 이상 열 수 없다 (기저 사례)
- 각 단계에서 인형의 크기가 **줄어든다** (종료 보장)

### Lean4에서의 재귀

Lean4는 **모든 재귀 함수가 반드시 종료**해야 한다. 이것은 무한 루프를 방지하며, Lean4의 증명 체계를 건전하게 유지한다. Lean4가 종료를 확인하는 방법:

1. **구조적 재귀**(structural recursion): 인수가 점점 "작아지는" 것을 패턴 매칭으로 확인
2. **`termination_by`**: 프로그래머가 종료 증거를 직접 제시

```lean
-- 구조적 재귀: Lean4가 자동으로 종료를 확인
-- n + 1 → n 으로 "줄어드는" 것이 명백
def countdown : Nat → List Nat
  | 0     => [0]                        -- 기저 사례
  | n + 1 => (n + 1) :: countdown n     -- 재귀: n+1 → n으로 감소

#eval countdown 5   -- [5, 4, 3, 2, 1, 0]
```

> 💡 **핵심**: 기저 사례가 없으면 Lean4는 컴파일을 **거부**한다. 이것이 재귀 알고리즘의 안전장치이다.

---

## 8F.2 팩토리얼 재귀 알고리즘 (Rosen 예제 1, 알고리즘 1)

### 수학적 정의

$n! = \begin{cases} 1 & \text{if } n = 0 \\ n \cdot (n-1)! & \text{if } n > 0 \end{cases}$

### Lean4 구현

```lean
def factorial : Nat → Nat
  | 0     => 1              -- 기저 사례: 0! = 1
  | n + 1 => (n + 1) * factorial n  -- 재귀: n! = n × (n-1)!

-- 실행 확인
#eval factorial 0   -- 1
#eval factorial 5   -- 120
#eval factorial 10  -- 3628800
```

### 실행 추적

`factorial 4`의 실행 과정을 추적해 보자:

```
factorial 4
= 4 * factorial 3
= 4 * (3 * factorial 2)
= 4 * (3 * (2 * factorial 1))
= 4 * (3 * (2 * (1 * factorial 0)))
= 4 * (3 * (2 * (1 * 1)))
= 4 * (3 * (2 * 1))
= 4 * (3 * 2)
= 4 * 6
= 24
```

총 **4번의 재귀 호출**이 일어났다. 일반적으로 `factorial n`은 **n번**의 재귀 호출을 사용한다.

### 연습 2-1: 팩토리얼 결과 확인 (괄호 채우기)

```lean
example : factorial 3 = (______) := by native_decide
example : factorial 6 = (______) := by native_decide
example : factorial 7 = (______) := by native_decide
```

<details>
<summary>💡 답 보기</summary>

```lean
example : factorial 3 = 6    := by native_decide
example : factorial 6 = 720  := by native_decide
example : factorial 7 = 5040 := by native_decide
```

</details>

### 연습 2-2: 팩토리얼의 기본 성질 (sorry 채우기)

```lean
-- 0! = 1
theorem factorial_zero : factorial 0 = 1 := by sorry

-- (n+1)! = (n+1) × n!
theorem factorial_succ (n : Nat) :
    factorial (n + 1) = (n + 1) * factorial n := by sorry

-- n! ≥ 1 (팩토리얼은 양수)
-- 이것은 귀납법으로 증명한다
theorem factorial_pos (n : Nat) : factorial n ≥ 1 := by sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
theorem factorial_zero : factorial 0 = 1 := by rfl

theorem factorial_succ (n : Nat) :
    factorial (n + 1) = (n + 1) * factorial n := by rfl

theorem factorial_pos (n : Nat) : factorial n ≥ 1 := by
  induction n with
  | zero => simp [factorial]
  | succ n ih =>
    simp [factorial]
    exact Nat.le_mul_of_pos_right _ (by omega)
```

**설명**:
- 처음 두 정리는 정의에 의해 자명하므로 `rfl`로 충분하다.
- `factorial_pos`는 귀납법으로: 기저 $0! = 1 ≥ 1$, 귀납 $(n+1)! = (n+1) \times n! ≥ 1 \times 1 = 1$.

</details>

---

## 8F.3 거듭제곱 재귀 알고리즘 (Rosen 예제 2, 알고리즘 2)

### 수학적 정의

$a^n = \begin{cases} 1 & \text{if } n = 0 \\ a \cdot a^{n-1} & \text{if } n > 0 \end{cases}$

### Lean4 구현

```lean
def myPow (a : Nat) : Nat → Nat
  | 0     => 1                  -- a⁰ = 1
  | n + 1 => a * myPow a n     -- aⁿ⁺¹ = a × aⁿ

-- 확인
#eval myPow 2 10   -- 1024
#eval myPow 3 5    -- 243
```

### 연습 3-1: 거듭제곱 확인 (sorry 채우기)

```lean
example : myPow 2 8 = 256 := by sorry
example : myPow 5 3 = 125 := by sorry
example : myPow 10 0 = 1  := by sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
example : myPow 2 8 = 256 := by native_decide
example : myPow 5 3 = 125 := by native_decide
example : myPow 10 0 = 1  := by rfl
```

</details>

### 빠른 거듭제곱 (효율적 재귀)

위의 `myPow`는 $n$번의 곱셈이 필요하다. **반복 제곱법**(repeated squaring)을 사용하면 $O(\log n)$번으로 줄일 수 있다:

$a^n = \begin{cases} 1 & \text{if } n = 0 \\ (a^{n/2})^2 & \text{if } n \text{이 짝수} \\ a \cdot (a^{(n-1)/2})^2 & \text{if } n \text{이 홀수} \end{cases}$

```lean
def fastPow (a : Nat) : Nat → Nat
  | 0 => 1
  | n + 1 =>
    if (n + 1) % 2 == 0 then
      let half := fastPow a ((n + 1) / 2)
      half * half
    else
      a * fastPow a n

-- 같은 결과를 훨씬 빠르게!
#eval fastPow 2 20    -- 1048576
#eval myPow 2 20      -- 1048576 (같은 결과, 더 느림)
```

> 💡 **효율 비교**:
>
> | 알고리즘 | `myPow 2 20` | `fastPow 2 20` |
> |---------|-------------|---------------|
> | 곱셈 횟수 | 20번 | ~5번 ($\log_2 20 ≈ 4.3$) |
> | 시간 복잡도 | $O(n)$ | $O(\log n)$ |

### 연습 3-2: 두 함수의 동등성 확인 (sorry 채우기)

```lean
-- 작은 값에서 두 함수가 같은 결과를 주는지 확인
example : fastPow 3 7 = myPow 3 7 := by sorry
example : fastPow 2 15 = myPow 2 15 := by sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
example : fastPow 3 7 = myPow 3 7 := by native_decide
example : fastPow 2 15 = myPow 2 15 := by native_decide
```

</details>

---

## 8F.4 최대공약수 재귀 알고리즘 (Rosen 예제 3, 알고리즘 3)

### 유클리드 알고리즘

**유클리드 알고리즘**(Euclidean algorithm)은 인류 역사상 가장 오래된 알고리즘 중 하나이다 (기원전 300년경):

$\gcd(a, b) = \begin{cases} a & \text{if } b = 0 \\ \gcd(b, a \bmod b) & \text{if } b > 0 \end{cases}$

### Lean4 구현

```lean
def myGcd : Nat → Nat → Nat
  | a, 0     => a                        -- 기저: gcd(a, 0) = a
  | a, b + 1 => myGcd (b + 1) (a % (b + 1))  -- 재귀: gcd(a, b) = gcd(b, a mod b)

-- 확인
#eval myGcd 12 8    -- 4
#eval myGcd 100 75  -- 25
#eval myGcd 252 198 -- 18
```

### 실행 추적: gcd(252, 198)

```
myGcd 252 198
= myGcd 198 (252 % 198)    -- 252 = 1×198 + 54
= myGcd 198 54
= myGcd 54 (198 % 54)      -- 198 = 3×54 + 36
= myGcd 54 36
= myGcd 36 (54 % 36)       -- 54 = 1×36 + 18
= myGcd 36 18
= myGcd 18 (36 % 18)       -- 36 = 2×18 + 0
= myGcd 18 0
= 18
```

### 왜 종료하는가?

유클리드 알고리즘이 종료하는 이유는 **두 번째 인수가 매번 줄어들기** 때문이다:

$$a \bmod b < b$$

이므로 $b$가 매 호출마다 **순감소**(strictly decreasing)한다. 자연수는 무한히 감소할 수 없으므로, 결국 $b = 0$에 도달하여 종료한다.

이것은 **순서화 성질**(well-ordering principle)의 직접적 응용이다! (Part 8-C에서 배운 내용)

### 연습 4-1: GCD 계산 (괄호 채우기)

```lean
example : myGcd 48 36 = (______) := by native_decide
example : myGcd 111 259 = (______) := by native_decide
example : myGcd 1000 625 = (______) := by native_decide
```

<details>
<summary>💡 답 보기</summary>

```lean
example : myGcd 48 36 = 12   := by native_decide
example : myGcd 111 259 = 37 := by native_decide
example : myGcd 1000 625 = 125 := by native_decide
```

</details>

### 연습 4-2: GCD와 Lean4 내장 함수 비교 (sorry 채우기)

```lean
-- Lean4 내장 Nat.gcd와 같은 결과인지 확인
example : myGcd 48 36 = Nat.gcd 48 36 := by sorry
example : myGcd 100 75 = Nat.gcd 100 75 := by sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
example : myGcd 48 36 = Nat.gcd 48 36 := by native_decide
example : myGcd 100 75 = Nat.gcd 100 75 := by native_decide
```

</details>

---

## 8F.5 이진 탐색 재귀 알고리즘 (Rosen 예제 4, 알고리즘 4)

### 이진 탐색이란?

**이진 탐색**(binary search)은 **정렬된 리스트**에서 값을 찾는 효율적 알고리즘이다. 리스트의 중간값과 비교하여 탐색 범위를 절반으로 줄인다.

| 알고리즘 | 탐색 방식 | 시간 복잡도 |
|---------|---------|----------|
| **선형 탐색**(linear search) | 하나씩 비교 | $O(n)$ |
| **이진 탐색**(binary search) | 절반씩 제거 | $O(\log n)$ |

1000개의 원소에서: 선형 탐색은 최대 1000번, 이진 탐색은 최대 10번!

### 의사코드 (Rosen 알고리즘 4)

```
procedure binary_search(x, a₁, a₂, ..., aₙ)
  i := 1, j := n
  while i < j
    m := ⌊(i + j) / 2⌋
    if x > aₘ then i := m + 1
    else j := m
  if x = aᵢ then location := i
  else location := 0
```

### Lean4 구현

```lean
-- 이진 탐색 (정렬된 배열에서)
def binarySearch (arr : Array Nat) (target : Nat) : Option Nat :=
  go 0 arr.size
where
  go (lo hi : Nat) : Option Nat :=
    if lo ≥ hi then none
    else
      let mid := (lo + hi) / 2
      if arr[mid]! == target then some mid
      else if arr[mid]! < target then go (mid + 1) hi
      else go lo mid
  termination_by hi - lo

-- 테스트
#eval binarySearch #[1, 3, 5, 7, 9, 11, 13] 7    -- some 3
#eval binarySearch #[1, 3, 5, 7, 9, 11, 13] 6    -- none
#eval binarySearch #[2, 4, 6, 8, 10, 12, 14] 10  -- some 4
```

> 💡 **`termination_by hi - lo`의 의미**:
>
> Lean4에게 "매 재귀 호출마다 `hi - lo`가 줄어든다"고 알려주는 것이다:
> - `go (mid + 1) hi`: 새로운 `lo` = `mid + 1` > `lo` → `hi - lo` 감소
> - `go lo mid`: 새로운 `hi` = `mid` < `hi` → `hi - lo` 감소
>
> 이것이 종료의 증거가 된다.

### 실행 추적: binarySearch #[1, 3, 5, 7, 9, 11, 13] 7

```
go 0 7            -- [1, 3, 5, 7, 9, 11, 13], mid = 3
  arr[3] = 7 == 7 → some 3  ✓ (한 번에 찾음!)
```

### 실행 추적: binarySearch #[1, 3, 5, 7, 9, 11, 13] 9

```
go 0 7            -- mid = 3, arr[3] = 7 < 9
  go 4 7          -- mid = 5, arr[5] = 11 > 9
    go 4 5        -- mid = 4, arr[4] = 9 == 9
      → some 4   ✓
```

### 연습 5-1: 이진 탐색 결과 예측 (괄호 채우기)

```lean
-- 정렬된 배열 [1, 5, 10, 15, 20, 25, 30]에서 탐색
def arr1 := #[1, 5, 10, 15, 20, 25, 30]

-- 15는 인덱스 3에 있다
example : binarySearch arr1 15 = some (______) := by native_decide

-- 25는 인덱스 ?에 있다
example : binarySearch arr1 25 = some (______) := by native_decide

-- 12는 없다
example : binarySearch arr1 12 = (______) := by native_decide
```

<details>
<summary>💡 답 보기</summary>

```lean
example : binarySearch arr1 15 = some 3 := by native_decide
example : binarySearch arr1 25 = some 5 := by native_decide
example : binarySearch arr1 12 = none    := by native_decide
```

</details>

---

## 8F.6 병합 정렬 (Rosen 예제 5, 알고리즘 5)

### 병합 정렬이란?

**병합 정렬**(merge sort)은 **분할 정복**(divide and conquer) 전략을 사용하는 정렬 알고리즘이다:

1. 리스트를 **절반**으로 나눈다
2. 각 절반을 **재귀적으로 정렬**한다
3. 정렬된 두 절반을 **병합**(merge)한다

시간 복잡도: $O(n \log n)$ — 버블 정렬의 $O(n^2)$보다 훨씬 빠르다!

### 핵심 보조 함수: merge

두 **이미 정렬된** 리스트를 하나의 정렬된 리스트로 합치는 함수이다:

```lean
-- 두 정렬된 리스트 병합
def merge : List Nat → List Nat → List Nat
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys =>
    if x ≤ y then
      x :: merge xs (y :: ys)
    else
      y :: merge (x :: xs) ys
termination_by xs ys => xs.length + ys.length
```

**merge의 작동 원리**:

```
merge [2, 5, 8] [1, 3, 9]
= 1 :: merge [2, 5, 8] [3, 9]     -- 1 < 2이므로 1 선택
= 1 :: 2 :: merge [5, 8] [3, 9]   -- 2 < 3이므로 2 선택
= 1 :: 2 :: 3 :: merge [5, 8] [9] -- 3 < 5이므로 3 선택
= 1 :: 2 :: 3 :: 5 :: merge [8] [9]
= 1 :: 2 :: 3 :: 5 :: 8 :: merge [] [9]
= 1 :: 2 :: 3 :: 5 :: 8 :: [9]
= [1, 2, 3, 5, 8, 9]
```

### 병합 정렬 본체

```lean
-- 병합 정렬
def mergeSort : List Nat → List Nat
  | [] => []
  | [x] => [x]
  | xs =>
    let mid := xs.length / 2
    let left := xs.take mid
    let right := xs.drop mid
    merge (mergeSort left) (mergeSort right)
termination_by xs.length

-- 테스트
#eval mergeSort [38, 27, 43, 3, 9, 82, 10]
-- [3, 9, 10, 27, 38, 43, 82]

#eval mergeSort [5, 3, 1, 4, 2]
-- [1, 2, 3, 4, 5]
```

### 실행 추적: mergeSort [38, 27, 43, 3]

```
mergeSort [38, 27, 43, 3]
  mid = 2
  left  = mergeSort [38, 27]
            mid = 1
            left  = mergeSort [38] = [38]    -- 기저 (원소 1개)
            right = mergeSort [27] = [27]    -- 기저
            merge [38] [27] = [27, 38]
  right = mergeSort [43, 3]
            mid = 1
            left  = mergeSort [43] = [43]    -- 기저
            right = mergeSort [3]  = [3]     -- 기저
            merge [43] [3] = [3, 43]
  merge [27, 38] [3, 43] = [3, 27, 38, 43]  -- 최종 병합
```

### 연습 6-1: merge 함수 이해 (괄호 채우기)

```lean
-- 두 정렬된 리스트의 병합 결과
example : merge [1, 3, 5] [2, 4, 6] = [1, 2, 3, 4, 5, (______)] := by native_decide

-- 빈 리스트와의 병합
example : merge [] [1, 2, 3] = (______) := by native_decide
example : merge [4, 5] [] = (______) := by native_decide
```

<details>
<summary>💡 답 보기</summary>

```lean
example : merge [1, 3, 5] [2, 4, 6] = [1, 2, 3, 4, 5, 6] := by native_decide
example : merge [] [1, 2, 3] = [1, 2, 3] := by native_decide
example : merge [4, 5] [] = [4, 5] := by native_decide
```

</details>

### 연습 6-2: 병합 정렬 결과 확인 (sorry 채우기)

```lean
example : mergeSort [10, 3, 7, 1, 8, 2] = [1, 2, 3, 7, 8, 10] := by sorry
example : mergeSort [5, 4, 3, 2, 1] = [1, 2, 3, 4, 5] := by sorry
example : mergeSort [1] = [1] := by sorry
example : mergeSort ([] : List Nat) = [] := by sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
example : mergeSort [10, 3, 7, 1, 8, 2] = [1, 2, 3, 7, 8, 10] := by native_decide
example : mergeSort [5, 4, 3, 2, 1] = [1, 2, 3, 4, 5] := by native_decide
example : mergeSort [1] = [1] := by rfl
example : mergeSort ([] : List Nat) = [] := by rfl
```

</details>

---

## 8F.7 재귀 알고리즘의 정확성 증명

### 왜 정확성 증명이 필요한가?

알고리즘이 "올바르게 동작한다"는 것은 직감이 아니라 **수학적 증명**으로 보여야 한다. 재귀 알고리즘의 정확성은 자연스럽게 **귀납법**으로 증명된다:

- 재귀 알고리즘의 **구조** = 재귀적 정의
- 정확성의 **증명** = 그 정의에 대한 귀납법

| 알고리즘의 부분 | 증명의 부분 |
|---------------|-----------|
| 기저 사례 | 귀납법의 기본 단계 |
| 재귀 호출이 올바르다는 가정 | 귀납 가정 |
| 전체가 올바름 | 귀납적 단계의 결론 |

### 예제 1: 팩토리얼의 정확성

"factorial n = n!"은 사실 정의 자체를 확인하는 것이지만, 재미있는 성질을 증명할 수 있다:

```lean
-- n! ≥ 1 (모든 n에 대해)
-- 이것은 귀납법의 전형적 응용
theorem factorial_ge_one : ∀ n : Nat, factorial n ≥ 1 := by
  intro n
  induction n with
  | zero => simp [factorial]      -- 0! = 1 ≥ 1
  | succ n ih =>
    -- ih : factorial n ≥ 1
    -- 목표: factorial (n + 1) ≥ 1
    simp [factorial]
    -- (n + 1) * factorial n ≥ 1
    -- n + 1 ≥ 1이고, factorial n ≥ 1이므로
    exact Nat.le_mul_of_pos_right _ (by omega)
```

### 예제 2: myPow의 정확성

`myPow a n = a ^ n`을 귀납법으로 증명해 보자:

```lean
-- myPow a n이 실제로 a^n인지 증명
theorem myPow_eq_pow (a n : Nat) : myPow a n = a ^ n := by
  induction n with
  | zero =>
    -- 기본 단계: myPow a 0 = 1 = a ^ 0
    simp [myPow]
  | succ n ih =>
    -- 귀납적 단계
    -- ih : myPow a n = a ^ n
    simp [myPow, pow_succ]
    -- 목표: a * myPow a n = a ^ n * a
    rw [ih]
    ring
```

### 연습 7-1: 구체적 정확성 확인 (sorry 채우기)

```lean
-- Lean4 내장 ^ 연산과 비교
example : myPow 2 5 = 2 ^ 5 := by sorry
example : myPow 3 4 = 3 ^ 4 := by sorry
example : myPow 1 100 = 1 ^ 100 := by sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
example : myPow 2 5 = 2 ^ 5 := by native_decide
example : myPow 3 4 = 3 ^ 4 := by native_decide
example : myPow 1 100 = 1 ^ 100 := by native_decide
```

</details>

### 예제 3: merge의 길이 보존

병합 정렬이 원소를 잃어버리지 않는지 확인하는 첫 걸음 — merge가 두 리스트의 원소를 모두 보존하는가?

```lean
-- merge의 결과 길이 = 두 입력 길이의 합
-- (구체적 값으로 확인)
example : (merge [1, 3] [2, 4]).length = [1, 3].length + [2, 4].length := by
  native_decide

example : (merge [1, 5, 9] [2]).length = [1, 5, 9].length + [2].length := by
  native_decide
```

### 연습 7-2: merge 길이 보존 확인 (sorry 채우기)

```lean
example : (merge [10, 20, 30] [5, 15, 25]).length = 6 := by sorry
example : (merge [] [1, 2, 3]).length = 3 := by sorry
example : (merge [7] []).length = 1 := by sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
example : (merge [10, 20, 30] [5, 15, 25]).length = 6 := by native_decide
example : (merge [] [1, 2, 3]).length = 3 := by native_decide
example : (merge [7] []).length = 1 := by native_decide
```

</details>

### 연습 7-3: mergeSort 길이 보존 (sorry 채우기)

정렬 후에도 원소의 개수가 같은가?

```lean
example : (mergeSort [3, 1, 4, 1, 5]).length = [3, 1, 4, 1, 5].length := by sorry
example : (mergeSort [10, 9, 8, 7]).length = 4 := by sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
example : (mergeSort [3, 1, 4, 1, 5]).length = [3, 1, 4, 1, 5].length := by native_decide
example : (mergeSort [10, 9, 8, 7]).length = 4 := by native_decide
```

</details>

---

## 8F.8 종합 연습 문제

### 도전 1: 피보나치와 재귀 (종합)

```lean
-- Part 8-D에서 정의한 피보나치
def fib : Nat → Nat
  | 0     => 0
  | 1     => 1
  | n + 2 => fib n + fib (n + 1)

-- 구체적 값 확인 (괄호 채우기)
example : fib 8 = (______) := by native_decide
example : fib 10 = (______) := by native_decide

-- fib n ≤ 2^n 확인 (sorry 채우기)
example : fib 5 ≤ 2 ^ 5 := by sorry
example : fib 10 ≤ 2 ^ 10 := by sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
example : fib 8 = 21 := by native_decide
example : fib 10 = 55 := by native_decide

example : fib 5 ≤ 2 ^ 5 := by native_decide
example : fib 10 ≤ 2 ^ 10 := by native_decide
```

</details>

### 도전 2: 자신만의 재귀 함수 (도전)

삼각수(triangular number) $T(n) = 1 + 2 + \cdots + n$을 재귀적으로 정의하고, $T(n) = n(n+1)/2$를 구체적 값으로 확인하시오:

```lean
-- 삼각수 재귀 정의
def triangular : Nat → Nat
  | 0     => sorry     -- T(0) = ?
  | n + 1 => sorry     -- T(n+1) = T(n) + (n+1)

-- 확인
example : triangular 5 = 15 := by sorry   -- 1+2+3+4+5 = 15
example : triangular 10 = 55 := by sorry  -- 1+2+...+10 = 55

-- T(n) = n*(n+1)/2 확인
example : triangular 100 = 100 * 101 / 2 := by sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
def triangular : Nat → Nat
  | 0     => 0
  | n + 1 => triangular n + (n + 1)

example : triangular 5 = 15 := by native_decide
example : triangular 10 = 55 := by native_decide
example : triangular 100 = 100 * 101 / 2 := by native_decide
```

</details>

### 도전 3: 재귀 vs 반복 (사고 문제)

다음 두 함수가 같은 결과를 주는지 확인하시오:

```lean
-- 재귀적 합
def sumRec : Nat → Nat
  | 0     => 0
  | n + 1 => (n + 1) + sumRec n

-- 공식을 직접 사용
def sumFormula (n : Nat) : Nat := n * (n + 1) / 2

-- 같은 결과인가?
example : sumRec 10 = sumFormula 10 := by sorry
example : sumRec 50 = sumFormula 50 := by sorry
example : sumRec 100 = sumFormula 100 := by sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
example : sumRec 10 = sumFormula 10 := by native_decide
example : sumRec 50 = sumFormula 50 := by native_decide
example : sumRec 100 = sumFormula 100 := by native_decide
```

**통찰**: 재귀적 합 `sumRec n`은 $O(n)$이고, 공식 `sumFormula n`은 $O(1)$이다. **같은 결과를 내지만 효율이 다르다**. 이것이 알고리즘 분석에서 중요한 교훈이다.

</details>

---

## 8F.9 전술 및 개념 종합 요약

### 재귀 알고리즘 핵심

| 개념 | 설명 |
|------|------|
| **재귀 알고리즘** | 문제를 더 작은 동일 문제로 분해하여 해결 |
| **기저 사례** | 더 이상 분해할 수 없는 최소 입력에 대한 직접 답 |
| **재귀 호출** | 자기 자신을 더 작은 입력으로 호출 |
| **종료성** | 입력이 매번 줄어들어 반드시 기저에 도달 |
| **정확성** | 귀납법으로 증명 (구조 = 재귀 → 증명 = 귀납) |

### 이 파트에서 구현한 알고리즘

| 알고리즘 | 시간 복잡도 | 핵심 아이디어 |
|---------|----------|------------|
| `factorial` | $O(n)$ | $n! = n \times (n-1)!$ |
| `myPow` | $O(n)$ | $a^n = a \times a^{n-1}$ |
| `fastPow` | $O(\log n)$ | $a^n = (a^{n/2})^2$ (반복 제곱법) |
| `myGcd` | $O(\log(\min(a,b)))$ | $\gcd(a,b) = \gcd(b, a \bmod b)$ |
| `binarySearch` | $O(\log n)$ | 중간값 비교로 절반 제거 |
| `mergeSort` | $O(n \log n)$ | 분할 + 재귀 정렬 + 병합 |

### Lean4 재귀 관련 키워드

| 키워드/전술 | 용도 |
|-----------|------|
| `def f : ... → ...` | 재귀 함수 정의 |
| 패턴 매칭 `\| 0 => ... \| n+1 => ...` | 기저 + 재귀 사례 분리 |
| `termination_by` | 종료 증거 제시 (비구조적 재귀) |
| `induction n with` | 재귀 함수에 대한 귀납법 증명 |
| `native_decide` | 구체적 계산 결과 검증 |
| `simp [f]` | 함수 정의를 펼쳐서 단순화 |
| `rw [ih]` | 귀납 가정으로 치환 |

---

## 5장 전체 요약: 귀납법과 재귀의 세계

5장(Part 8 시리즈)을 통해 배운 내용을 한눈에 정리하면:

| 파트 | 주제 | 핵심 도구 |
|------|------|---------|
| **8-A** | 수학적 귀납법 | `induction n with \| zero => \| succ n ih =>` |
| **8-B** | 귀납법 연습 | 합 공식, 부등식, 나눗셈 증명 |
| **8-C** | 강 귀납법 | 모든 이전 값을 가정으로 사용 |
| **8-C2** | 강 귀납법 연습 | 우표 문제, 소인수 존재 |
| **8-D** | 재귀적 정의 | `def f`, `inductive`, 피보나치 |
| **8-E** | 구조적 귀납법 | 이진 트리, 체계화 공식 |
| **8-F** | 재귀 알고리즘 | 팩토리얼, GCD, 병합 정렬 |

> 💡 **대통합**: 귀납법과 재귀는 **동전의 양면**이다:
>
> | | 재귀 | 귀납법 |
> |---|------|--------|
> | 방향 | 큰 것 → 작은 것 (분해) | 작은 것 → 큰 것 (축적) |
> | 용도 | **정의**와 **계산** | **증명** |
> | 핵심 | "작은 문제를 먼저 풀자" | "작은 경우가 참이면 큰 경우도 참" |
> | Lean4 | `def` + 패턴 매칭 | `induction` 전술 |

---

**(끝)**
