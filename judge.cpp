#include <bits/stdc++.h>

#define ff first
#define ss second
#define mp make_pair

using namespace std;

char s[100005], t[100005], f[100005];

bool fileSat(char *f){
	int n = strlen(f);
	for(int i = 0; i < n-1; i++)
		if(f[i] == '_' && f[i+1] == 'n')
			return 1;
	return 0;
}

int main(){

	FILE *fp;

	fp = fopen("x.log", "r");
	if(!fp) return 0;

	int cnt = 0, tot = 0, n, ptr;
	// vector<pair<string, pair<int, pair<string, string> > > > v;
	vector<pair<string, pair<string, string> > > v;
	while(fscanf(fp, " Processing file ../../JoseMarcos/lwb/%s %s %[^\n]", s, t, f) == 3){
		tot++;

		n = strlen(s);
		// s[n-4] = 0;
		// ptr = n-4;
		// while(s[ptr-1] != '.') ptr--;
		// s[ptr-1] = 0;

		v.push_back(mp(s, mp(t, f)));
		// v.push_back(mp(s, mp(atoi(s+ptr), mp(t, f))));
		// s[ptr-1] = '.';
		// s[n-7] = '.';
		if(!strcmp(t, "Unable")) continue;
		cnt++;
		bool satf = fileSat(s);
		bool satr = t[0] == 'S';
		if(satf != satr) printf("%s\n", s);
	}
	// sort(v.begin(), v.end());

	// for(int i = 0; i < (int)v.size(); i++)
	// 	printf("%s.%d.kps\n%s\n%s\n\n", v[i].ff.c_str(), v[i].ss.ff, v[i].ss.ss.ff.c_str(), v[i].ss.ss.ss.c_str());

	// for(int i = 0; i < (int)v.size(); i++)
	// 	printf("%s\n%s\n%s\n\n", v[i].ff.c_str(), v[i].ss.ff.c_str(), v[i].ss.ss.c_str());

	printf("Finished in %d/%d\n", cnt, tot);

	fclose(fp);

	return 0;
}