// Deterministic scan sharing plus one edge repair; finite screening only.
#include <array>
#include <vector>
#include <iostream>
#include <fstream>
#include <algorithm>
#include <unordered_set>
#include <string>
#include "phase_screen.hpp"
static Machine baseline;
static std::vector<Fixture> fixtures;
static long long evaluations=0;
int core_count=0;
int core_score(const Machine&m,int dead,int keep) {
 int s=0;for(int i=0;i<core_count;i++){if(!run(m,dead,keep,fixtures[i]))break;s++;}return s;
}
Machine merged(int dead,int keep){Machine m=baseline;for(auto&r:m)for(auto&e:r)if(e.q==dead)e.q=keep;return m;}
void save(const Machine&m,int dead,int keep,int start,const std::string&path){
 std::ofstream o(path);o<<"{\"removed\":"<<dead<<",\"merged_into\":"<<keep<<",\"start\":"<<start<<",\"table\":[";
 for(int q=0;q<25;q++){if(q)o<<',';o<<'[';for(int b=0;b<2;b++){if(b)o<<',';auto e=m[q][b];o<<'['<<e.w<<','<<e.d<<','<<e.q<<']';}o<<']';}o<<"]}\n";
}
std::string key(const Machine&m,int dead,int start){
 std::string s;s.push_back(start-(start>dead));
 for(int q=0;q<25;q++)if(q!=dead)for(auto e:m[q]){
  s.push_back(e.w+1);s.push_back(e.d+1);s.push_back(e.q<0?0:e.q-(e.q>dead)+1);
 }return s;
}
int main(int argc,char**argv){
 if(argc!=2){std::cerr<<"Usage: search_scans OUTPUT_DIRECTORY < INPUT\n";return 2;}
 for(auto&r:baseline)for(auto&e:r)if(!(std::cin>>e.w>>e.d>>e.q))return 2;
 int total;std::cin>>core_count>>total;
 for(int i=0;i<total;i++){Fixture f;std::cin>>f.kind>>f.n>>f.p>>f.success>>f.baseline_steps;fixtures.push_back(f);}
 if(core_score(baseline,-1,-1)!=core_count){std::cerr<<"Baseline core fixtures failed\n";return 2;}
 for(int i=core_count;i<total;i++)if(!run(baseline,-1,-1,fixtures[i]))return 2;
 std::string out=argv[1];
 std::unordered_set<std::string> found;
 long long core_pass=0,boot_pass=0,outer_pass=0;int hits=0;
 auto evaluate=[&](const Machine&m,int dead,int keep){
  evaluations++;int s=core_score(m,dead,keep);
  if(s<core_count)return;core_pass++;
  for(int start=0;start<25;start++)if(start!=dead){
   Fixture boot{0,0,0,true,45};
   if(!run(m,dead,keep,boot,3,start))continue;
   boot_pass++;
   bool good=true;for(int i=core_count;i<total;i++)if(!run(m,dead,keep,fixtures[i])){good=false;break;}
   if(!good)continue;outer_pass++;
   if(found.insert(key(m,dead,start)).second){
    hits++;save(m,dead,keep,start,out+"/candidate-"+std::to_string(hits)+".json");
    std::cout<<"Candidate "<<hits<<": remove "<<dead<<", start "<<start<<std::endl;
   }
  }
 };
 std::vector<std::pair<int,int>> pairs;
 for(auto group:std::vector<std::vector<int>>{{13,14,16,18,20,23},{11,19,21,22},{5,7,8}})
  for(int d:group)for(int k:group)if(d!=k)pairs.push_back({d,k});
 for(auto [dead,keep]:pairs){
  Machine base=merged(dead,keep);evaluate(base,dead,keep);
  for(int q=0;q<25;q++)if(q!=dead)for(int b=0;b<2;b++)
   for(int t=0;t<25;t++)if(t!=dead)for(int w=0;w<2;w++)for(int d:{-1,1}){
    Edge e{w,d,t};if(e==base[q][b])continue;
    Machine m=base;m[q][b]=e;evaluate(m,dead,keep);
   }
 }
 std::ofstream report(out+"/summary.json");
 report<<"{\"ordered_scan_pairs\":"<<pairs.size()<<",\"evaluations\":"<<evaluations
 <<",\"simulated_steps\":"<<steps_run<<",\"core_fixtures\":"<<core_count
 <<",\"outer_fixtures\":"<<total-core_count<<",\"core_passes\":"<<core_pass
 <<",\"bootstrap_passes\":"<<boot_pass<<",\"outer_passes\":"<<outer_pass
 <<",\"distinct_finite_survivors\":"<<hits<<"}\n";
 std::cout<<"Finished "<<evaluations<<" candidates; "<<hits<<" distinct finite survivors."<<std::endl;
}
