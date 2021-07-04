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
      
      if(type == 2) {

        // Assigning Ip to all the devices which don't have ip 

      }

      if(type == 4) {
        runner = false;
      }
    }

    // cout<<"Devices : ";
    // for(ll i=0;i<hub_list.size();i++) {
    //     cout<<"Global index : "<<hub_list[i].global_index<<"\n";
    //     cout<<"Mac address : "<<hub_list[i].mac <<" ";
    //     cout<<"\n";
    //     cout<<"\n";
    // }
    // cout<<"\n";
    // cout<<"Hubs : ";
    // for(ll i=0;i<hub_list.size();i++) {
    //     cout<<"Global Index : "<<hub_list[i].global_index<<" ";
    //     cout<<"Mac address : "<<hub_list[i].mac <<" ";
    //     cout<<"\n";
    //     cout<<"\n";
    // }
    // cout<<"\n";
    // cout<<"Switches  : ";
    // for(ll i=0;i<switch_list.size();i++) {
    //     cout<<"Global Index : "<<switch_list[i].global_index<<" ";
    //     cout<<"Mac address : "<<switch_list[i].mac <<" ";
    //     cout<<"\n";
    //     cout<<"\n";
    // }
    // cout<<"\n";
    // cout<<"Router : ";
    // for(ll i=0;i<router_list.size();i++) {
    //     cout<<router_list[i].global_index<<" ";
    //     for(ll j=0;j<router_list[i].interface_ip_mac.size();j++) {
    //       cout<<router_list[i].interface_ip_mac[j].first<<" "<<router_list[i].interface_ip_mac[j].second<<"\n";
    //     }
    //     cout<<"\n";
    //     cout<<"\n";
    // }
    // cout<<"\n";


    // for(ll i = 0;i < m; i++) {
    //     cinll(u);cinll(v);
    //     addEdge(u,v);
    // }
    vector<bool> visited(n+1,false);
    dfs(1,visited);

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


