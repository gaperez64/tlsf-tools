#include "tlsf/gr1_lift.h"
#include <chrono>
#include <fstream>
#include <iostream>
#include <iterator>
#include <string>

static void write(const std::string &path,const char *data,size_t size){
  if(!data)return;
  std::ofstream file(path,std::ios::binary);
  file.write(data,static_cast<std::streamsize>(size));
  if(!file)throw std::runtime_error("cannot write artifact");
}
int main(int argc,char **argv){
  if(argc<2 || argc>4){std::cerr<<"usage: native_lift INPUT [OUTPUT-PREFIX] [SECONDS]\n";return 2;}
  std::ifstream file(argv[1],std::ios::binary);
  if(!file){std::cerr<<"cannot read input\n";return 2;}
  std::string bytes(std::istreambuf_iterator<char>{file},{});
  TlsfGr1LiftOptions options{};
  options.abi_version=TLSF_GR1_LIFT_ABI_VERSION;
  options.struct_size=sizeof options;
  options.solver_nodes=1u<<18;options.solver_cache=1u<<16;
  options.checker_nodes=1u<<18;options.checker_cache=1u<<16;
  options.schema_nodes=1u<<18;options.schema_cache=1u<<16;
  options.max_artifact_bytes=4u<<20;
  options.max_monitor_states=1000;
  double seconds=argc==4?std::stod(argv[3]):15;
  auto now=std::chrono::steady_clock::now().time_since_epoch();
  options.deadline_mono_ns=std::chrono::duration_cast<std::chrono::nanoseconds>(now).count()+
                           uint64_t(seconds*1e9);
  TlsfGr1LiftResult result{};
  TlsfGr1LiftError error{};
  auto status=tlsf_gr1_lift_v1(reinterpret_cast<const uint8_t *>(bytes.data()),
                               bytes.size(),nullptr,0,&options,&result,&error);
  std::cout<<"status="<<status<<" stage="<<error.stage<<" message="<<error.message<<"\n";
  if(status==TLSF_GR1_LIFT_OK){
    std::cout<<"method="<<result.method<<" verdict="<<result.verdict<<"\n";
    std::cout.write(result.evidence_json,result.evidence_size);std::cout<<"\n";
    if(argc>=3){
      std::string prefix=argv[2];
      write(prefix+".game.aag",result.game_aag,result.game_size);
      write(prefix+".cert.aag",result.certificate_aag,result.certificate_size);
      write(prefix+".cert.json",result.certificate_json,result.certificate_json_size);
      write(prefix+".policy.aag",result.policy_aag,result.policy_size);
      write(prefix+".policy.json",result.policy_json,result.policy_json_size);
      write(prefix+".check.json",result.check_json,result.check_json_size);
      write(prefix+".evidence.json",result.evidence_json,result.evidence_size);
    }
  }
  tlsf_gr1_lift_result_clear(&result);
  return status==TLSF_GR1_LIFT_OK?0:status==TLSF_GR1_LIFT_DECLINED?3:4;
}
