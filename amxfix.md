Thanks — the test case itself is perfectly fine. The **bug isn’t here** — it’s almost certainly in how `AccelerateSparseSolver::solve()` converts Eigen’s matrix into an Accelerate `SparseMatrixStructure`.

Because Eigen stores **both triangles** and Accelerate’s Cholesky requires **only the upper triangle (and consistent CSC indices)**, your conversion step is likely producing:

* duplicate entries, **or**
* mismatched `columnStarts / rowIndices / nz`.

Let’s reason from your matrix.

---

## What Accelerate *expects* for this matrix (CSC, upper-triangle only)

Matrix:

```
[ 4 1 0
  1 4 1
  0 1 4 ]
```

Upper triangle entries (i ≤ j):

```
(0,0)=4
(0,1)=1
(1,1)=4
(1,2)=1
(2,2)=4
```

So:

```
n  = 3
nz = 5      <-- NOT 7
```

### Correct CSC layout

**columnStarts (length n+1 = 4)**
indexes into row array:

```
col: [0, 2, 4, 5]
```

Meaning:

* column 0 occupies row[0..1]
* column 1 occupies row[2..3]
* column 2 occupies row[4..4]

**rowIndices (length nz = 5)**:

```
row: [0,        // (0,0)
      0,        // (0,1)
      1,        // (1,1)
      1,        // (1,2)
      2]        // (2,2)
```

(no lower-triangle entries; strictly sorted within columns)

If instead your converter sent *all 7 triplets*, then symbolic-Cholesky sees:

* lower-triangle entries it **doesn’t expect**
* structural duplication of symmetric elements
* `nz=7` but structure described as symmetric/upper

…and it crashes exactly where you saw it.

---

## What to fix inside `AccelerateSparseSolver::solve`

In your converter, before filling Accelerate arrays:

### ✔️ Filter to upper triangle

```cpp
if (i <= j) {
    // keep (i,j)
}
```

### ✔️ Use `long` arrays

```cpp
std::vector<long> colStarts(n + 1);
std::vector<long> rowIndices(nz);
```

### ✔️ Set structure explicitly

```cpp
structure.structureType    = SparseSymmetric;
structure.symmetricStorage = SparseUpperTriangular;
structure.rowCount = n;
structure.columnCount = n;
structure.rowIndices = rowIndices.data();
structure.columnStarts = colStarts.data();
```

Do **not** pass a general matrix type to Cholesky.

---

## A compact Eigen→Accelerate conversion pattern (safe)

```cpp
Eigen::SparseMatrix<double> U = A.selfadjointView<Eigen::Upper>();

U.makeCompressed();

long n  = U.rows();
long nz = U.nonZeros();

SparseMatrixStructure S;
S.structureType    = SparseSymmetric;
S.symmetricStorage = SparseUpperTriangular;
S.rowCount         = n;
S.columnCount      = n;
S.columnStarts     = (long*)U.outerIndexPtr();
S.rowIndices       = (long*)U.innerIndexPtr();
```

(Accelerate’s CSC matches Eigen’s column-major compressed layout — once you drop the lower triangle.)

> Key trick: `selfadjointView<Eigen::Upper>()` removes duplicates and guarantees valid upper-triangle CSC.

---

## Why Eigen works but Accelerate crashed

Eigen’s LLT can internally reconcile symmetry and duplicates.
Accelerate assumes you already gave it a **clean symmetric structure**. If not, it walks off into invalid memory → `EXC_BAD_ACCESS` in `_SparseSymbolicFactorSymmetric`.

---

## If you want, paste your `accelerate_solver.cpp`

Specifically the code around:

```
SparseFactor(...)
```

and the struct preparation. I’ll annotate the exact lines to change.

But I’m 99% sure:

> **You passed all 7 triplets to a routine that requires only the 5 upper-triangle entries, and maybe with 32-bit indices.**

Fix those, and this test should pass — your Eigen result and Accelerate result should match to machine precision.
