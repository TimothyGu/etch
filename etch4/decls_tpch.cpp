// TPC-H decls
// sorry

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "sqlite3.h"

constexpr int TPCH_ARRAY_SIZE = 10000000;

// populated later
int tpch_lineitem1_pos[TPCH_ARRAY_SIZE];  // orderkey
int tpch_lineitem1_crd[TPCH_ARRAY_SIZE];
int tpch_lineitem2_pos[TPCH_ARRAY_SIZE];  // suppkey
int tpch_lineitem2_crd[TPCH_ARRAY_SIZE];
double tpch_lineitem_extendedprice[TPCH_ARRAY_SIZE];
double tpch_lineitem_discount[TPCH_ARRAY_SIZE];

// tpch_customer1 = custkey (dense)
int tpch_customer2_pos[TPCH_ARRAY_SIZE];  // nationkey
int tpch_customer2_crd[TPCH_ARRAY_SIZE];

// tpch_orders1 = orderkey (dense)
int tpch_orders2_pos[TPCH_ARRAY_SIZE];  // custkey
int tpch_orders2_crd[TPCH_ARRAY_SIZE];

// tpch_supplier1 = suppkey (dense)
int tpch_supplier2_pos[TPCH_ARRAY_SIZE];  // nationkey
int tpch_supplier2_crd[TPCH_ARRAY_SIZE];

// tpch_nation1 = nationkey (dense)
int tpch_nation2_pos[TPCH_ARRAY_SIZE];  // regionkey
int tpch_nation2_crd[TPCH_ARRAY_SIZE];

// tpch_region1 = regionkey (dense)
int tpch_region2_pos[TPCH_ARRAY_SIZE];  // regionkey
char* tpch_region2_crd[TPCH_ARRAY_SIZE];

#define GEN_MAT_COL_INIT(tbl_name, idx, col_name, copy) \
  tbl_name##_##col_name[tbl_name##2_pos [tbl_name##1_pos [1]] - 1] = 0

#define GEN_MAT_COL_SET(tbl_name, idx, col_name, copy)                \
  tbl_name##_##col_name[tbl_name##2_pos [tbl_name##1_pos [1]] - 1] += \
      copy(argv[idx])

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

// this is sparse-sparse, aka "dcsr"
#define GEN_SS(tbl_name, crd1eq, crd1conv, crd1copy, crd2eq, crd2conv,      \
               crd2copy, cols)                                              \
  static int gen_##tbl_name##_callback(void* data, int argc, char** argv,   \
                                       char** azColName) {                  \
    if (tbl_name##1_pos [0] == tbl_name##1_pos [1] ||                       \
        !crd1eq(crd1conv(argv[0]),                                          \
                tbl_name##1_crd [tbl_name##1_pos [1] - 1])) {               \
      tbl_name##1_pos [1] = (tbl_name##1_pos [1] + 1);                      \
      tbl_name##2_pos [((tbl_name##1_pos [1] - 1) + 1)] =                   \
          tbl_name##2_pos [(tbl_name##1_pos [1] - 1)];                      \
    }                                                                       \
    tbl_name##1_crd [tbl_name##1_pos [1] - 1] = crd1copy(argv[0]);          \
                                                                            \
    if (tbl_name##2_pos [tbl_name##1_pos [1] - 1] ==                        \
            tbl_name##2_pos [tbl_name##1_pos [1]] ||                        \
        !crd2eq(                                                            \
            crd2conv(argv[1]),                                              \
            tbl_name##2_crd [tbl_name##2_pos [tbl_name##1_pos [1]] - 1])) { \
      tbl_name##2_pos [tbl_name##1_pos [1]] += 1;                           \
      cols(GEN_MAT_COL_INIT);                                               \
    }                                                                       \
                                                                            \
    tbl_name##2_crd [tbl_name##2_pos [tbl_name##1_pos [1]] - 1] =           \
        crd2copy(argv[1]);                                                  \
    cols(GEN_MAT_COL_SET);                                                  \
                                                                            \
    return 0;                                                               \
  }

#define EQ(a, b) (a == b)
#define STR_EQ(a, b) (strcmp(a, b) == 0)
#define ID(a) (a)

#define lineitem_cols(f)                    \
  f(tpch_lineitem, 2, extendedprice, atof); \
  f(tpch_lineitem, 3, discount, atof);
GEN_SS(tpch_lineitem, EQ, atoi, atoi, EQ, atoi, atoi, lineitem_cols)

#define no_cols(f)
GEN_DS(tpch_customer, EQ, atoi, atoi, no_cols)
GEN_DS(tpch_orders, EQ, atoi, atoi, no_cols)
GEN_DS(tpch_supplier, EQ, atoi, atoi, no_cols)
GEN_DS(tpch_nation, EQ, atoi, atoi, no_cols)
GEN_DS(tpch_region, STR_EQ, ID, strdup, no_cols)

namespace {

int populate_tpch(sqlite3* db) {
  char* zErrMsg;
  int rc;
  void* data = nullptr;

#define GET_MAT2(tbl_name, col1, col2, ...)                                  \
  rc = sqlite3_exec(db,                                                     \
                    "SELECT " #col1 ", " #col2 ", " #__VA_ARGS__            \
                    " FROM " #tbl_name " ORDER BY " #col1 ", " #col2,       \
                    gen_tpch_##tbl_name##_callback, (void*)data, &zErrMsg); \
  if (rc != SQLITE_OK) {                                                    \
    printf("%s:%d: %s\n", __FILE__, __LINE__, zErrMsg);                     \
    return rc;                                                              \
  }

#define GET_TBL2(tbl_name, col1, col2)                                      \
  rc = sqlite3_exec(db,                                                     \
                    "SELECT " #col1 ", " #col2 " FROM " #tbl_name           \
                    " ORDER BY " #col1 ", " #col2,                          \
                    gen_tpch_##tbl_name##_callback, (void*)data, &zErrMsg); \
  if (rc != SQLITE_OK) {                                                    \
    printf("%s:%d: %s\n", __FILE__, __LINE__, zErrMsg);                     \
    return rc;                                                              \
  }

  GET_MAT2(lineitem, l_orderkey, l_suppkey, l_extendedprice, l_discount)
  GET_TBL2(customer, c_custkey, c_nationkey)
  GET_TBL2(orders, o_orderkey, o_custkey)
  GET_TBL2(supplier, s_suppkey, s_nationkey)
  GET_TBL2(nation, n_nationkey, n_regionkey)
  GET_TBL2(region, r_regionkey, r_name)

  return rc;
}
}  // namespace
