import sys
import os
import json
import statistics

target_path = sys.argv[1]
files = os.listdir(target_path)
for f_name in files:
    print ("========processing file " + f_name)
    results_info = json.load(open(target_path + f_name))
    stage1_t = []
    stage2_t = []
    stage3_t = []
    query_time = []
    verify_time = []
    vo_size = []
    for res_info in results_info:
        query_info = res_info['query_info']
        verify_info = res_info['verify_info']
        stage1_t.append(int(query_info['stage1']['real']))
        stage2_t.append(int(query_info['stage2']['real']))
        stage3_t.append(int(query_info['stage3']['real']))
        query_time.append(int(query_info['total']['real']))
        verify_time.append(int(verify_info['verify_time']['real']))
        vo_size.append(int(verify_info['vo_size']))
    avg_stg1 = statistics.mean(stage1_t)
    avg_stg2 = statistics.mean(stage2_t)
    avg_stg3 = statistics.mean(stage3_t)
    avg_query_t = statistics.mean(query_time)
    avg_verify_t = statistics.mean(verify_time)
    avg_vo_size = statistics.mean(vo_size)
    print ("stage1: " + str(avg_stg1) + "us")
    print ("stage2: " + str(avg_stg2) + "us")
    print ("stage3: " + str(avg_stg3) + "us")
    print ("query: " + str(avg_query_t) + "us")
    print ("verify: " + str(avg_verify_t) + "us")
    print ("VO: " + str(avg_vo_size) + "bytes")
