import sys
import os
import json
import statistics
import csv

DB_DIR='eth_small_254'
q_dirs = next(os.walk('./data/query/generated_query/'))[1]
db_dirs = next(os.walk('./data/db/'+DB_DIR))[1]

output = '../vchain_plus_exp_res.csv'
head = ['', 'stage1', 'stage2', 'stage3', 'query_t', 'verify_t', 'total_vo_s', 'cur_id_s', 'merkle_s', 'trie_proof_s', 'vo_dag_s', 'id_proof_s']
with open(output,'a') as f:
    writer = csv.writer(f)
    writer.writerow(head)
    for db in db_dirs:
        files = os.listdir('./data/result/'+DB_DIR+'/'+db+'/')
        for f in files:
            file_path = './data/result/'+DB_DIR+'/'+db+'/'+f
            file_id = db+'_'+f
            file_id = file_id.replace('.json', '')
            print ("========processing file " + file_path)
            results_info = json.load(open(file_path))
            stage1_t = []
            stage2_t = []
            stage3_t = []
            query_time = []
            verify_time = []
            total_vo_size = []
            cur_id_s = []
            merkle_s = []
            trie_proof_s = []
            vo_dag_s = []
            id_proof_s = []
            for res_info in results_info:
                query_info = res_info['query_info']
                verify_info = res_info['verify_info']
                stage1_t.append(int(query_info['stage1']['real']))
                stage2_t.append(int(query_info['stage2']['real']))
                stage3_t.append(int(query_info['stage3']['real']))
                query_time.append(int(query_info['total']['real']))
                verify_time.append(int(verify_info['verify_time']['real']))
                total_vo_size.append(int(verify_info['vo_size']['total_s']))
                cur_id_s.append(int(verify_info['vo_size']['cur_id_s']))
                merkle_s.append(int(verify_info['vo_size']['merkle_s']))
                trie_proof_s.append(int(verify_info['vo_size']['trie_proof_s']))
                vo_dag_s.append(int(verify_info['vo_size']['vo_dag_s']))
                id_proof_s.append(int(verify_info['vo_size']['id_proof_s']))
            avg_stg1 = statistics.mean(stage1_t) / 1000
            avg_stg2 = statistics.mean(stage2_t) / 1000
            avg_stg3 = statistics.mean(stage3_t) / 1000
            avg_query_t = statistics.mean(query_time) / 1000
            avg_verify_t = statistics.mean(verify_time) / 1000
            avg_total_vo_size = statistics.mean(total_vo_size)
            avg_cur_id_s = statistics.mean(cur_id_s)
            avg_merkle_s = statistics.mean(merkle_s)
            avg_trie_proof_s = statistics.mean(trie_proof_s)
            avg_vo_dag_s = statistics.mean(vo_dag_s)
            avg_id_proof_s = statistics.mean(id_proof_s)
            row = [file_id, avg_stg1, avg_stg2, avg_stg3, avg_query_t, avg_verify_t, avg_total_vo_size, avg_cur_id_s, avg_merkle_s, avg_trie_proof_s, avg_vo_dag_s, avg_id_proof_s]
            writer.writerow(row)
            print ("stage1: " + str(avg_stg1) + "ms")
            print ("stage2: " + str(avg_stg2) + "ms")
            print ("stage3: " + str(avg_stg3) + "ms")
            print ("query: " + str(avg_query_t) + "ms")
            print ("verify: " + str(avg_verify_t) + "ms")
            print ("VO: " + str(avg_vo_size) + "bytes")

# target_path = sys.argv[1]
# files = os.listdir(target_path) # os.listdir will list files and dirs
# for f_name in files:
#     print ("========processing file " + f_name)
#     results_info = json.load(open(target_path + f_name))
#     stage1_t = []
#     stage2_t = []
#     stage3_t = []
#     query_time = []
#     verify_time = []
#     vo_size = []
#     for res_info in results_info:
#         query_info = res_info['query_info']
#         verify_info = res_info['verify_info']
#         stage1_t.append(int(query_info['stage1']['real']))
#         stage2_t.append(int(query_info['stage2']['real']))
#         stage3_t.append(int(query_info['stage3']['real']))
#         query_time.append(int(query_info['total']['real']))
#         verify_time.append(int(verify_info['verify_time']['real']))
#         vo_size.append(int(verify_info['vo_size']))
#     avg_stg1 = statistics.mean(stage1_t)
#     avg_stg2 = statistics.mean(stage2_t)
#     avg_stg3 = statistics.mean(stage3_t)
#     avg_query_t = statistics.mean(query_time)
#     avg_verify_t = statistics.mean(verify_time)
#     avg_vo_size = statistics.mean(vo_size)
#     print ("stage1: " + str(avg_stg1) + "us")
#     print ("stage2: " + str(avg_stg2) + "us")
#     print ("stage3: " + str(avg_stg3) + "us")
#     print ("query: " + str(avg_query_t) + "us")
#     print ("verify: " + str(avg_verify_t) + "us")
#     print ("VO: " + str(avg_vo_size) + "bytes")
