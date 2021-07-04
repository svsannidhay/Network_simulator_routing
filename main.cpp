///////////////////////////////////////////////////////////////////////////////////////////////////
#include <iostream>
#include <vector>
#include <algorithm>
#include <stack>
#include <queue>
#include <map>
#include <math.h>
#include <climits>
#include <set>
#include <cstring>
#include <unordered_map>
#include <cstdlib>
#include <cmath>
#include <string>
#include <iomanip>
#include <cmath>
#include <bitset>
#include <stdlib.h>
#include <chrono>


///////////////////////////////////////////////////////////////////////////////////////////////////
#define fio  ios_base::sync_with_stdio(false);cin.tie(NULL);
#define ll  long long int
#define ull unsigned long long int
#define cinll(x) ll x;cin >> x;
#define cini(x) int x;cin >> x;
#define cins(x) string x;cin >> x;
#define vect(x) vector<ll> x
#define vect1(x) vector<ll> x;x.push_back(0);
#define pb(x) push_back(x)
#define mp(x, y) make_pair(x, y)
///////////////////////////////////////////////////////////////////////////////////////////////////
#define MAX 1e17
#define MIN -9223372036854775800
#define MOD 1000000007
#define f first
#define s second
///////////////////////////////////////////////////////////////////////////////////////////////////
using namespace std;
using u64 = uint64_t;
//Safe_hashing for minimising collisions 
//https://codeforces.com/blog/entry/62393
struct custom_hash {
    static uint64_t splitmix64(uint64_t x) {
        // http://xorshift.di.unimi.it/splitmix64.c
        x += 0x9e3779b97f4a7c15;
        x = (x ^ (x >> 30)) * 0xbf58476d1ce4e5b9;
        x = (x ^ (x >> 27)) * 0x94d049bb133111eb;
        return x ^ (x >> 31);
    }
    size_t operator()(uint64_t x) const {
        static const uint64_t FIXED_RANDOM = chrono::steady_clock::now().time_since_epoch().count();
        return splitmix64(x + FIXED_RANDOM);
    }
};

/////// NID FINDER 


///////////////////////////////////////// DEVICES SUPPORTED ////////////////////////////////////////
class Host{
  public:
    ll global_index;
    string mac;
    string ipv4;
    string subnet;
    string nid;
    string gateway_mac;
    unordered_map<string,string> arp_table;
};

class Hub{
  public:
    ll global_index;
    string mac;
};

class Switch{
  public:
    ll global_index;
    string mac;
    // Hashed Switch table for O(1) look up time 
    // Mapping mac address to the port of the switch
    unordered_map<string,ll> switch_table;
};

class Router{
  public: 
    ll global_index;
    ll no_of_interfaces;
    vector< pair<pair<string,string>,string> > interface_ip_mac;
};

///////////////////////////////////////MAC ADDRESS GENERATION //////////////////////////////////////////
// currently supporting 65,565 different addresses 
vector< string > mac_address_list;
ll mac_index;

string to_hex(ll x) {
    string hex;
    if(x <= 9) {
        hex = to_string(x);
    }
    if(x == 10) hex = "A";
    if(x == 11) hex = "B";
    if(x == 12) hex = "C";
    if(x == 13) hex = "D";
    if(x == 14) hex = "E";
    if(x == 15) hex = "F";
    return hex;
}

string create_add(string add,ll i,ll j,ll k,ll l) {
    add += to_hex(i);
    add += to_hex(j);
    add.pb(':');
    add += to_hex(k);
    add += to_hex(l);
    return add;
}

void generate_mac_address() {
    ll count = 0;
    string add = "00:AA:BB:00:";
    for(ll i = 0;i < 16; i++) {
        for(ll j = 0;j < 16; j++) {
            for(ll k = 0; k < 16; k++) {
                for(ll l = 0; l < 16; l++) {
                    string full_add = create_add(add,i,j,k,l);
                    mac_address_list.pb(full_add);
                }
            }
        }
    }
}

//////////////////////////////////////////////////////////////////////////////////////////////////

bitset<32> ip_bits(string ip) {
  
  bitset<32> bset;

  ll bit = 31;

  ll start = 0;
  string current = "";
  while(start < ip.length()) {
    if(ip[start] == '.') {
      ll val = stoi(current);
      bitset<8> bset2(val);
      ll s = 7;
      while(s >= 0) {
        bset[bit] = bset2[s];
        bit--;
        s--;
      }
      current = "";
    } else {
      current.push_back(ip[start]);
    }
    start++;
  }
  ll val = stoi(current);
  bitset<8> bset2(val);
  ll s = 7;
  while(s >= 0) {
    bset[bit] = bset2[s];
    bit--;
    s--;
  }
  current = "";

  // cout<<bset;

  return bset;
}

///////////////////////////////////FINDING NID ///////////////////////////////////////////////////

string find_nid(string ip,string subn) {

  bitset<32> bitsip = ip_bits(ip);
  bitset<32> subnet = ip_bits(subn);

  bitset<32> nid = bitsip & subnet;

  string nids;

  ll ind = 7;
  bitset<8> nidbits;

  for(ll i = 31;i >= 0; i--) {
    if(ind == -1) {
      ind = 7;
      ll val = nidbits.to_ulong(); 
      nids += to_string(val);
      nids.pb('.');
      bitset<8> newb;
      nidbits = newb; 
    }
    nidbits[ind] = nid[i];
    ind--;
  }
  ll val = nidbits.to_ulong();
  nids += to_string(val);
  return nids;
}

//////////////////////////////////////////////////////////////////////////////////////////////////

///////////////////////////////////Physical Topology//////////////////////////////////////////////

// Network 
//Saving the whole topology as a graph (adjacency list)
vector< ll > connections[1001];

// Adding connections 
// duplex connection 
void addEdge(ll u,ll v) {
    connections[u].pb(v);
    connections[v].pb(u);
}

// we will map each device to its type
unordered_map< ll , pair<string,ll> > device_type;

// Caching the data of each device 
vector<Host> host_list;
ll host_no;
vector<Hub> hub_list;
ll hub_no;
vector<Switch> switch_list;
ll switch_no;
vector<Router> router_list;
ll router_no;

//////////////////////////////////////////////////////////////////////////////////////////////////


//////////////////////////////////////////////////////////////////////////////////////////////////


///////////////////////////////////////////DEBUGGER///////////////////////////////////////////////

void dfs(ll current_device, vector<bool> & visited) {
    if(!visited[current_device]) {
        visited[current_device] = true;

        string type = device_type[current_device].f;
        if( type == "Host") {
            Host h = host_list[device_type[current_device].s];
            cout<<"global index : "<<h.global_index<<"\n";
            cout<<"mac address : "<<h.mac<<"\n";
            cout<<"device type : "<<type<<"\n\n";
        } else if(type == "Hub") {
            Hub h = hub_list[device_type[current_device].s];
            cout<<"global index : "<<h.global_index<<"\n";
            cout<<"mac address : "<<h.mac<<"\n";
            cout<<"device type : "<<type<<"\n\n";
        } else if(type == "Switch") {
            Switch s = switch_list[device_type[current_device].s];
            cout<<"global index : "<<s.global_index<<"\n";
            cout<<"mac address : "<<s.mac<<"\n";
            cout<<"device type : "<<type<<"\n\n";
        } else if(type == "Router") {
            Router b = router_list[device_type[current_device].s];
            cout<<"global index : "<<b.global_index<<"\n";
            cout<<"interface list : \n";
            for(ll i=0;i<b.interface_ip_mac.size();i++) {
              cout<<b.interface_ip_mac[i].first.first<<" : "<<b.interface_ip_mac[i].first.second<<" "<<b.interface_ip_mac[i].second<<"\n"; 
            }
            cout<<"device type : "<<type<<"\n\n";
        }

        for(ll i = 0;i < connections[current_device].size(); i++) {
            if(!visited[connections[current_device][i]]) {
                dfs(connections[current_device][i],visited);
            }
        }
    }
}


/////////////////////////////////////////////////////////////////////////////////////////////////

void arp_request(ll current_device, vector<bool> & visited,string ip_dest,string &mac_dest) {
  if(!visited[current_device]) {
        visited[current_device] = true;
        string type = device_type[current_device].f;
        if(type == "Host") {
          int h_index = device_type[current_device].s;
          Host h = host_list[h_index];
          if(h.ipv4 == ip_dest) {
            vector<bool> vis(visited.size(),false);
            cout<<"Host found !!!!!!";
            mac_dest = h.mac;
            return;
          }
        }

        if(type == "Router") {
          Router r = router_list[device_type[current_device].s];
          for(ll i = 0;i < r.interface_ip_mac.size();i++) {
            if(r.interface_ip_mac[i].f.f == ip_dest) {
              vector<bool> vis(visited.size(),false);
              cout<<"Gateway Found !!!!";
              mac_dest =  r.interface_ip_mac[i].s;
              return;
            }
          }
        }

        if(type != "Router") {
          for(ll i = 0;i < connections[current_device].size(); i++) {
              if(!visited[connections[current_device][i]]) {
                arp_request(connections[current_device][i],visited,ip_dest,mac_dest);
              }
          }
        }
        return;
    }
}

////////////////////////////////ARP Table //////////////////////////////////////////////////////
// runs only when both sender and destination are in same subnet

string search_mac(ll current_device, string ip_Address) {
  unordered_map<string,string> arp_table = host_list[device_type[current_device].s].arp_table;
  string mac_dest = "";
  for(auto it = arp_table.begin(); it != arp_table.end(); it++) {
    if(it->first == ip_Address) {
      return it->second;
    }
  }
  vector<bool> visited(1000,false);
  arp_request(current_device, visited ,ip_Address, mac_dest);
  return mac_dest;
}


////////////////////////////////Routing (OSPF) //////////////////////////////////////////////////


////////////////////////////////SEND PACKETS (BOTH DATA AND ACK) /////////////////////////////////


// void send_packet(ll current_device,vector <bool> &visited, string sender_ip , string dest_ip , string)
 

//////////////////////////////////////////////////////////////////////////////////////////////////


/////////////////////////////////////// NETWORK BOOTER ////////////////////////////////////////// 
// Assign's MAC addresses and create the graph to represent the whole network


void boot() {
    ll n = 0;

    cout<<"////// -> To Add a device enter 1. (Format : devicetype index) \n";
    cout<<"////// -> To Add a connection enter 2. \n";
    cout<<"///// -> To Run a query enter 3. \n";
    cout<<"//// To exit enter  4 \n";
    bool runner = true;


    while(runner) {
      cinll(type);
      // Entering a device
      if(type == 1) {
        cout<<"Enter device and its global index : ";
        cins(device); cinll(index);
        n = max(n,index);
        cout<<"\n";
        if(device == "Host") {
          Host h;
          h.global_index = index;
          h.mac = mac_address_list[mac_index];
          device_type[index] = mp(device,host_no);
          mac_index++;
          cout<<"IP Address : ";
          cin>>h.ipv4;
          cout<<"\n";
          cout<<"Subnet Mask : ";
          cin>>h.subnet;
          cout<<"\n";
          host_list.pb(h);
          host_no++;
        }

        if(device == "Switch") {
          Switch s;
          s.global_index = index;
          s.mac = mac_address_list[mac_index];
          mac_index++;
          switch_list.pb(s);
          device_type[index] = mp(device,switch_no);
          switch_no++;
        } 

        if(device == "Hub") {
          Hub h;
          h.global_index = index;
          h.mac = mac_address_list[mac_index];
          mac_index++;
          device_type[index] = mp(device,hub_no);
          hub_no++;
          hub_list.pb(h);
        }

        if(device == "Router") {
          cout<<"Enter the maximum no of iterfaces need : ";
          cinll(no);
          cout<<"\n";
          Router r;
          r.global_index = index;
          ll curr = 0;
          while(no > 0) {
            cout<<"ip for interface " << curr << " : ";
            cins(ip);
            cout<<"Subnet for interface " << curr <<" : ";
            cins(subnet);
            cout<<"\n";
            r.interface_ip_mac.pb(mp(mp(ip,subnet),mac_address_list[mac_index]));
            mac_index++;
            curr++;
            no--;
          } 
          device_type[index] = mp(device,router_no);
          router_list.pb(r);
          router_no++;
        }

      }

      if(type == 2) {
        cout<<"Enter the connection (u,v) : ";
        cinll(u);cinll(v);
        cout<<"\n";
        addEdge(u,v);

      }
      
      if(type == 3) {
        cout<<"Enter source's global_index : ";
        cinll(ind);
        cout<<"Enter source's IP : ";
        cins(ips);
        cout<<"Enter source's subnet : ";
        cins(subnets);
        cout<<"\n";

        cout<<"Enter destination's IP : ";
        cins(ipd);
        cout<<"Enter destination's subnet :";
        cins(subnetd);

        if(find_nid(ips,subnets) == find_nid(ipd,subnetd)) {
          cout<<"Source and destination are in same subnet \n";
          cout<<search_mac(ind,ipd);
        } else {
          cout<<"Source and destination are in different subnet";
        }

      }

      if(type == 4) {
        runner = false;
      }
    }


    // vector<bool> visited(n+1,false);
    // dfs(1,visited);

}



void solve() {
    generate_mac_address();
    boot();
    // run_network();
    // no_of_collision_domains();
    return;
}    

int main(){
    // fio;
    // cinll(t);
///////////////////////////////////////////    
    // #ifndef ONLINE_JUDGE
    // freopen("input.txt" , "r", stdin);
    // freopen("output.txt", "w" , stdout);
    // #endif
///////////////////////////////////////////
    // cinll(t);
    // for(ll i=1;i<=t;i++) {
        solve();
    // }
  return 0;
}


