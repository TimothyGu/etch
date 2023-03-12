// TPC-H decls
// This is technically a C file, but it works in C++ too.

#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "sqlite3.h"

#define TPCH_SF 4

// populated later
int tpch_lineitem1_pos[TPCH_SF * 1500000 + 10];  // orderkey
int tpch_lineitem1_crd[TPCH_SF * 1500000 + 10];
int tpch_lineitem2_pos[TPCH_SF * 1500000 + 10];  // suppkey
int tpch_lineitem2_crd[TPCH_SF * 6010000 + 10];
double tpch_lineitem_extendedprice[TPCH_SF * 6010000 + 10];
double tpch_lineitem_discount[TPCH_SF * 6010000 + 10];

// tpch_customer1 = custkey (dense)
int tpch_customer2_pos[TPCH_SF * 150000 + 10];  // nationkey
int tpch_customer2_crd[TPCH_SF * 150000 + 10];

// tpch_orders1 = orderkey (dense)
int tpch_orders2_pos[TPCH_SF * 6010000 + 10];  // orderdate
int tpch_orders2_crd[TPCH_SF * 1500000 + 10];
int tpch_orders3_pos[TPCH_SF * 1500000 + 10];  // custkey
int tpch_orders3_crd[TPCH_SF * 1500000 + 10];

// tpch_supplier1 = suppkey (dense)
int tpch_supplier2_pos[TPCH_SF * 10000 + 10];  // nationkey
int tpch_supplier2_crd[TPCH_SF * 10000 + 10];

// tpch_nation1 = nationkey (dense)
int tpch_nation2_pos[25 + 10];  // regionkey
int tpch_nation2_crd[25 + 10];

// tpch_region1 = regionkey (dense)
int tpch_region2_pos[5 + 10];  // regionkey
char* tpch_region2_crd[5 + 10];

#define GEN_MAT_COL_INIT(tbl_name, idx, col_name, copy) \
  tbl_name##_##col_name[tbl_name##2_pos [tbl_name##1_pos [1]] - 1] = 0

#define GEN_MAT_COL_SET(tbl_name, idx, col_name, copy)                \
  tbl_name##_##col_name[tbl_name##2_pos [tbl_name##1_pos [1]] - 1] += \
      copy(argv[idx])

#define GEN_MAT3_COL_INIT(tbl_name, idx, col_name, copy) \
  tbl_name##_##col_name                                  \
      [tbl_name##3_pos [tbl_name##2_pos [atoi(argv[0]) + 1]] - 1] = 0;

#define GEN_MAT3_COL_SET(tbl_name, idx, col_name, copy)              \
  tbl_name##_##col_name                                              \
      [tbl_name##3_pos [tbl_name##2_pos [atoi(argv[0]) + 1]] - 1] += \
      copy(argv[idx]);

// this is dense-sparse, aka "csr"
#define GEN_DS(tbl_name, crd2eq, crd2conv, crd2copy, cols)                     \
  static int tbl_name##_i1_ = 0;                                               \
  static int gen_##tbl_name##_callback(void* data, int argc, char** argv,      \
                                       char** azColName) {                     \
    while (tbl_name##_i1_ <= atoi(argv[0])) {                                  \
      tbl_name##2_pos [tbl_name##_i1_ + 1] = tbl_name##2_pos [tbl_name##_i1_]; \
      tbl_name##_i1_ += 1;                                                     \
    }                                                                          \
    if (tbl_name##2_pos [atoi(argv[0])] ==                                     \
            tbl_name##2_pos [atoi(argv[0]) + 1] ||                             \
        !crd2eq(crd2conv(argv[1]),                                             \
                tbl_name##2_crd [tbl_name##2_pos [atoi(argv[0]) + 1] - 1])) {  \
      tbl_name##2_pos [atoi(argv[0]) + 1] += 1;                                \
      cols(GEN_MAT_COL_INIT);                                                  \
    }                                                                          \
    tbl_name##2_crd [tbl_name##2_pos [atoi(argv[0]) + 1] - 1] =                \
        crd2copy(argv[1]);                                                     \
    cols(GEN_MAT_COL_SET);                                                     \
                                                                               \
    return 0;                                                                  \
  }

#define PRINT_LENGTH_DS(tbl_name)                                         \
  do {                                                                    \
    printf("%s2_pos: %d\n", #tbl_name, tbl_name##_i1_ + 1);               \
    printf("%s2_crd: %d\n", #tbl_name, tbl_name##2_pos [tbl_name##_i1_]); \
  } while (false)

// this is sparse-sparse, aka "dcsr"
// "is_set" controls whether we assume input keys will be unique
#define GEN_SS(tbl_name, is_set, crd1eq, crd1conv, crd1copy, crd2eq, crd2conv, \
               crd2copy, cols)                                                 \
  static int tbl_name##_out = 0;                                               \
  static int gen_##tbl_name##_callback(void* data, int argc, char** argv,      \
                                       char** azColName) {                     \
    tbl_name##_out++;                                                          \
    if (tbl_name##1_pos [0] == tbl_name##1_pos [1] ||                          \
        !crd1eq(crd1conv(argv[0]),                                             \
                tbl_name##1_crd [tbl_name##1_pos [1] - 1])) {                  \
      tbl_name##1_pos [1] += 1;                                                \
      tbl_name##2_pos [tbl_name##1_pos [1]] =                                  \
          tbl_name##2_pos [tbl_name##1_pos [1] - 1];                           \
    }                                                                          \
    tbl_name##1_crd [tbl_name##1_pos [1] - 1] = crd1copy(argv[0]);             \
                                                                               \
    if (!is_set ||                                                             \
        tbl_name##2_pos [tbl_name##1_pos [1] - 1] ==                           \
            tbl_name##2_pos [tbl_name##1_pos [1]] ||                           \
        !crd2eq(                                                               \
            crd2conv(argv[1]),                                                 \
            tbl_name##2_crd [tbl_name##2_pos [tbl_name##1_pos [1]] - 1])) {    \
      tbl_name##2_pos [tbl_name##1_pos [1]] += 1;                              \
      cols(GEN_MAT_COL_INIT);                                                  \
    }                                                                          \
                                                                               \
    tbl_name##2_crd [tbl_name##2_pos [tbl_name##1_pos [1]] - 1] =              \
        crd2copy(argv[1]);                                                     \
    cols(GEN_MAT_COL_SET);                                                     \
                                                                               \
    return 0;                                                                  \
  }

#define PRINT_LENGTH_SS(tbl_name)                                              \
  do {                                                                         \
    printf("%s total: %d\n", #tbl_name, tbl_name##_out);                       \
    printf("%s1_pos: %d\n", #tbl_name, 1 + 1);                                 \
    printf("%s1_crd: %d\n", #tbl_name, tbl_name##1_pos [1]);                   \
    printf("%s2_pos: %d\n", #tbl_name, tbl_name##1_pos [1] + 1);               \
    printf("%s2_crd: %d\n", #tbl_name, tbl_name##2_pos [tbl_name##1_pos [1]]); \
  } while (false)

#define GEN_DSS(tbl_name, crd2eq, crd2conv, crd2copy, cols)                    \
  static int tbl_name##_i1_ = 0;                                               \
  static int gen_##tbl_name##_callback(void* data, int argc, char** argv,      \
                                       char** azColName) {                     \
    while ((tbl_name##_i1_ <= atoi(argv[0]))) {                                \
      tbl_name##2_pos [tbl_name##_i1_ + 1] = tbl_name##2_pos [tbl_name##_i1_]; \
      tbl_name##_i1_ += 1;                                                     \
    }                                                                          \
    if (tbl_name##2_pos [atoi(argv[0])] ==                                     \
            tbl_name##2_pos [atoi(argv[0]) + 1] ||                             \
        !crd2eq(crd2conv(argv[1]),                                             \
                tbl_name##2_crd [tbl_name##2_pos [atoi(argv[0]) + 1] - 1])) {  \
      tbl_name##2_pos [atoi(argv[0]) + 1] += 1;                                \
      tbl_name##3_pos [tbl_name##2_pos [atoi(argv[0]) + 1]] =                  \
          tbl_name##3_pos [tbl_name##2_pos [atoi(argv[0]) + 1] - 1];           \
    }                                                                          \
    tbl_name##2_crd [tbl_name##2_pos [atoi(argv[0]) + 1] - 1] =                \
        crd2copy(argv[1]);                                                     \
    if (tbl_name##3_pos [tbl_name##2_pos [atoi(argv[0]) + 1] - 1] ==           \
            tbl_name##3_pos [tbl_name##2_pos [atoi(argv[0]) + 1]] ||           \
        atoi(argv[2]) !=                                                       \
            tbl_name##3_crd                                                    \
                [tbl_name##3_pos [tbl_name##2_pos [atoi(argv[0]) + 1]] - 1]) { \
      tbl_name##3_pos [tbl_name##2_pos [atoi(argv[0]) + 1]] += 1;              \
      cols(GEN_MAT3_COL_INIT);                                                 \
    }                                                                          \
    tbl_name##3_crd [tbl_name##3_pos [tbl_name##2_pos [atoi(argv[0]) + 1]] -   \
                     1] = atoi(argv[2]);                                       \
    cols(GEN_MAT3_COL_SET);                                                    \
    return 0;                                                                  \
  }

#define PRINT_LENGTH_DSS(tbl_name)                                            \
  do {                                                                        \
    printf("%s2_pos: %d\n", #tbl_name, tbl_name##_i1_ + 1);                   \
    printf("%s2_crd: %d\n", #tbl_name, tbl_name##2_pos [tbl_name##_i1_]);     \
    printf("%s3_pos: %d\n", #tbl_name, tbl_name##2_pos [tbl_name##_i1_] + 1); \
    printf("%s3_crd: %d\n", #tbl_name,                                        \
           tbl_name##3_pos [tbl_name##2_pos [tbl_name##_i1_]]);               \
  } while (false)

#define EQ(a, b) (a == b)
#define STR_EQ(a, b) (strcmp(a, b) == 0)
#define ID(a) (a)

#define lineitem_cols(f)                    \
  f(tpch_lineitem, 2, extendedprice, atof); \
  f(tpch_lineitem, 3, discount, atof);
GEN_SS(tpch_lineitem, false, EQ, atoi, atoi, EQ, atoi, atoi, lineitem_cols)

#define no_cols(f)
GEN_DS(tpch_customer, EQ, atoi, atoi, no_cols)
GEN_DSS(tpch_orders, EQ, atoi, atoi, no_cols)
GEN_DS(tpch_supplier, EQ, atoi, atoi, no_cols)
GEN_DS(tpch_nation, EQ, atoi, atoi, no_cols)
GEN_DS(tpch_region, STR_EQ, ID, strdup, no_cols)

static int populate_tpch(sqlite3* db) {
  char* zErrMsg;
  int rc;
  void* data = NULL;

#define GET_MAT2(tbl_name, col1, col2, ...)                                   \
  do {                                                                        \
    rc = sqlite3_exec(db,                                                     \
                      "SELECT " #col1 ", " #col2 ", " #__VA_ARGS__            \
                      " FROM " #tbl_name " ORDER BY 1, 2",                    \
                      gen_tpch_##tbl_name##_callback, (void*)data, &zErrMsg); \
    if (rc != SQLITE_OK) {                                                    \
      printf("%s:%d: %s\n", __FILE__, __LINE__, zErrMsg);                     \
      return rc;                                                              \
    }                                                                         \
  } while (false)

#define GET_TBL2(tbl_name, col1, col2)                                      \
  do {                                                                      \
    rc = sqlite3_exec(                                                      \
        db, "SELECT " #col1 ", " #col2 " FROM " #tbl_name " ORDER BY 1, 2", \
        gen_tpch_##tbl_name##_callback, (void*)data, &zErrMsg);             \
    if (rc != SQLITE_OK) {                                                  \
      printf("%s:%d: %s\n", __FILE__, __LINE__, zErrMsg);                   \
      return rc;                                                            \
    }                                                                       \
  } while (false)

#define GET_TBL3(tbl_name, col1, col2, col3)                                   \
  do {                                                                         \
    rc = sqlite3_exec(db,                                                      \
                      "SELECT " #col1 ", " #col2 ", " #col3 " FROM " #tbl_name \
                      " ORDER BY 1, 2, 3",                                     \
                      gen_tpch_##tbl_name##_callback, (void*)data, &zErrMsg);  \
    if (rc != SQLITE_OK) {                                                     \
      printf("%s:%d: %s\n", __FILE__, __LINE__, zErrMsg);                      \
      return rc;                                                               \
    }                                                                          \
  } while (false)

  GET_MAT2(lineitem, l_orderkey, l_suppkey, l_extendedprice, l_discount);
  GET_TBL2(customer, c_custkey, c_nationkey);
  GET_TBL3(orders, o_orderkey, unixepoch(o_orderdate, 'utc'), o_custkey);
  GET_TBL2(supplier, s_suppkey, s_nationkey);
  GET_TBL2(nation, n_nationkey, n_regionkey);
  GET_TBL2(region, r_regionkey, r_name);

  PRINT_LENGTH_SS(tpch_lineitem);
  PRINT_LENGTH_DSS(tpch_orders);
  PRINT_LENGTH_DS(tpch_customer);
  PRINT_LENGTH_DS(tpch_supplier);
  PRINT_LENGTH_DS(tpch_nation);
  PRINT_LENGTH_DS(tpch_region);

  return rc;
}
