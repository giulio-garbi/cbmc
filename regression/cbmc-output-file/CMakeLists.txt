add_test_pl_tests(
    "${CMAKE_CURRENT_SOURCE_DIR}/chain.py $<TARGET_FILE:cbmc>" "-f"
)
