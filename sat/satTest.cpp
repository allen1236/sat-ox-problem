#include <iostream>
#include <vector>
#include "sat.h"
#include <iomanip>

#include <ctime>


using namespace std;

#define O 'o'
#define X 'x'

int Buff;
int Len;

void
initLayer(SatSolver& solver, vector<Var>& s, vector<Var>& o, vector<Var>& x, int n )
{
	s.reserve(Len);
	o.reserve(Len);
	x.reserve(Len);

	for( int i=0; i<2*n; i++ )
	{
		s.push_back( solver.newVar() );
		solver.assertProperty( s[i], false );
		o.push_back( solver.newVar() );
		solver.assertProperty( o[i], (i%2) );
		x.push_back( solver.newVar() );
		solver.assertProperty( x[i], !(i%2) );

	}
	for( int i=2*n; i<Len; i++ )
	{
		s.push_back( solver.newVar() );
		solver.assertProperty( s[i], true );
		o.push_back( solver.newVar() );
		solver.assertProperty( o[i], false );
		x.push_back( solver.newVar() );
		solver.assertProperty( x[i], false );
	}
}

void unique( SatSolver& solver, vector<Var>& vars, bool exactOne=true )
{
	int n = vars.size();

	vector<Lit> ls;
	vec<Lit> l;
	ls.resize(n);

	for( int i=0; i<n; i++ ) {
		ls[i] =  Lit(vars[i]);
		l.push(ls[i]);
	}
	if (exactOne) solver.addClause(l);

	l.clear();

	for ( int i=0; i<n-1; i++ ) {
		for (int j=i+1; j<n; j++ ) {
			l.push(~ls[i]); l.push(~ls[j]); solver.addClause(l); l.clear();
		}
	}
}

void
transLayer( 
		SatSolver& solver,
		vector<Var>& s,
		vector<Var>& o,
		vector<Var>& x,
		vector<Var>& sn,
		vector<Var>& on,
		vector<Var>& xn,
		vector<Var>& t,
		vector<Var>& p,
		const int k, 
		const int n
		)
{

	sn.reserve( Len );
	on.reserve( Len );
	xn.reserve( Len );

	t.reserve( Len );

	vector<Var> vars;
	int count = (n+1)/2;

	for( int i=0; i<Len; i++ )
	{
		sn.push_back(solver.newVar());
		on.push_back(solver.newVar());
		xn.push_back(solver.newVar());
		t.push_back(solver.newVar());

		vars.push_back(sn[i]);
		vars.push_back(on[i]);
		vars.push_back(xn[i]);

		unique( solver, vars );
		vars.clear();
	}


	unique( solver, t );

	// temp holder
	Var y[2];
	Lit ly[2];
	for ( int i=0; i<2; i++ )
	{
		y[i] = solver.newVar();
		ly[i] = Lit(y[i]);
	}

	// take rule
	for ( int i=1; i<Len-2; i++)
	{
		vec<Lit> l;

		Lit lt=Lit(t[i]),
			ls0=Lit(s[i]),
			ls1=Lit(s[i+1]),
			lo0=Lit(o[i]),
			lo1=Lit(o[i+1]),
			lof=Lit(o[i-1]),
			lob=Lit(o[i+2]),
			lx0=Lit(x[i]),
			lx1=Lit(x[i+1]),
			lxf=Lit(x[i-1]),
			lxb=Lit(x[i+2]),
			lsn0=Lit(sn[i]),
			lsn1=Lit(sn[i+1]);

		l.push(~lt); 
		l.push(~ls0); solver.addClause(l); l.pop(); 
		l.push(~ls1); solver.addClause(l); l.pop();
		l.push(lsn0); solver.addClause(l); l.pop();
		l.push(lsn1); solver.addClause(l); l.pop();
		l.push(~ly[0]); l.push(lo0); solver.addClause(l); l.pop(); l.pop();
		l.push(ly[0]); l.push(lx0); solver.addClause(l); l.pop(); l.pop();
		l.push(~ly[1]); l.push(lo1); solver.addClause(l); l.pop(); l.pop();
		l.push(ly[1]); l.push(lx1); solver.addClause(l); l.pop(); l.pop();

		if ( (n%2) && k==count-1 ) {
			l.push(~ly[0]); l.push(lof); solver.addClause(l); l.pop(); l.pop();
			l.push(ly[0]); l.push(lxf); solver.addClause(l); l.pop(); l.pop();
		} else {
			l.push(~ly[0]); l.push(lxf); solver.addClause(l); l.pop(); l.pop();
			l.push(ly[0]); l.push(lof); solver.addClause(l); l.pop(); l.pop();
		}

		l.push(~ly[1]); l.push(lxb); solver.addClause(l); l.pop(); l.pop();
		l.push(ly[1]); l.push(lob); solver.addClause(l); l.pop(); l.pop();



		l.clear();
	}

	// place rule
	for ( int i=1; i<Len-2; i++ )
	{
		vec<Lit> l;

		Lit lp=Lit(p[i]),
			ls0=Lit(s[i]),
			ls1=Lit(s[i+1]),
			lon0=Lit(on[i]),
			lon1=Lit(on[i+1]),
			lonf=Lit(on[i-1]),
			lonb=Lit(on[i+2]),
			lxn0=Lit(xn[i]),
			lxn1=Lit(xn[i+1]),
			lxnf=Lit(xn[i-1]),
			lxnb=Lit(xn[i+2]),
			lsn0=Lit(sn[i]),
			lsn1=Lit(sn[i+1]);

		l.push(~lp); 
		l.push(ls0); solver.addClause(l); l.pop(); 
		l.push(ls1); solver.addClause(l); l.pop();
		l.push(~lsn0); solver.addClause(l); l.pop();
		l.push(~lsn1); solver.addClause(l); l.pop();
		l.push(~ly[0]); l.push(lon0); solver.addClause(l); l.pop(); l.pop();
		l.push(ly[0]); l.push(lxn0); solver.addClause(l); l.pop(); l.pop();
		l.push(~ly[1]); l.push(lon1); solver.addClause(l); l.pop(); l.pop();
		l.push(ly[1]); l.push(lxn1); solver.addClause(l); l.pop(); l.pop();

		l.push(~ly[0]); l.push(lonf); solver.addClause(l); l.pop(); l.pop();
		l.push(ly[0]); l.push(lxnf); solver.addClause(l); l.pop(); l.pop();

		if ( !(n%2) && k==count ) {
			l.push(~ly[1]); l.push(lxnb); solver.addClause(l); l.pop(); l.pop();
			l.push(ly[1]); l.push(lonb); solver.addClause(l); l.pop(); l.pop();
		} else {
			l.push(~ly[1]); l.push(lonb); solver.addClause(l); l.pop(); l.pop();
			l.push(ly[1]); l.push(lxnb); solver.addClause(l); l.pop(); l.pop();
		}

		l.clear();

	}

	// stay rule
	for ( int i=1; i<Len-1; i++ )
	{

		vec<Lit> l;

		Lit lp=Lit(p[i]),
			lt=Lit(t[i]),
			lo0=Lit(o[i]),
			lx0=Lit(x[i]),
			ls0=Lit(s[i]),
			lon0=Lit(on[i]),
			lxn0=Lit(xn[i]),
			lsn0=Lit(sn[i]);

		l.push(lp); l.push(lt);
		l.push(Lit(p[i-1])); l.push(Lit(t[i-1]));
		l.push(~lo0); l.push(lon0); solver.addClause(l); l.pop(); l.pop();
		l.push(~lx0); l.push(lxn0); solver.addClause(l); l.pop(); l.pop();
		l.push(~ls0); l.push(lsn0); solver.addClause(l); l.pop(); l.pop();
		
		l.clear();
	}


	// assert (head and tail of t and p)
	solver.assertProperty( t[0], false );
	solver.assertProperty( t[Len-1], false );
	solver.assertProperty( t[Len-2], false );
	solver.assertProperty( t[Len-4], false );

	solver.assertProperty( xn[Len-1], true );
	solver.assertProperty( xn[0], true );

	if (k<count) {
		solver.assertProperty( y[0], !(k%2) );
		solver.assertProperty( y[1], k%2 );
	} else {
		solver.assertProperty( y[0], !((n+k)%2) );
		solver.assertProperty( y[1], !((n+k)%2) );
	}
	

}

void
finalLayer(
		SatSolver& solver,
		vector<Var>& s,
		vector<Var>& o,
		vector<Var>& x,
		const int n
		)
{

	// the second last layer
	for( int i=0; i<Len; i++ ) {
		if (i==Len-2 || i==Len-3 ) solver.assertProperty( s[i], true );
		else if (i>1 && i<n+2) solver.assertProperty( o[i], true );
		else solver.assertProperty( x[i], true );
	} 

}

void
genProofModel(SatSolver& solver, 
		vector<vector<Var> > &s,
		vector<vector<Var> > &o,
		vector<vector<Var> > &x,
		vector<vector<Var> > &t,
		int n)
{
	// added: pair rule
	s.resize(n);
	o.resize(n);
	x.resize(n);
	t.resize(n);


	initLayer( solver, s[0], o[0], x[0], n );


	
	vector<Var> p;
	for (int i=0; i<Len; i++) {
		p.push_back(solver.newVar());
		solver.assertProperty(p[i], (i==Len-2)?true:false );
	}
	transLayer( solver, s[0], o[0], x[0], s[1], o[1], x[1], t[0], p, 0, n );

	for ( int i=1; i<n-1; i++ )
		transLayer( solver, s[i], o[i], x[i], s[i+1], o[i+1], x[i+1], t[i], t[i-1], i, n );

	finalLayer( solver, s[n-1], o[n-1], x[n-1], n );


	// support rules
	solver.assertProperty(o[1][Len-2] ,true);
	solver.assertProperty(x[1][Len-1] ,true);

	// unique position between each placement
	solver.assertProperty( t[n-2][Len-3], true );
	for( int i=0; i<Len-1; i++ ) {
		vector<Var> v;
		v.reserve(n-1);
		for ( int j=0; j<n-1; j++ )  {
			v.push_back(t[j][i]);
		}
		unique(solver, v, false);
	}

}

void reportResult(
		const SatSolver& solver,
		vector<vector<Var> > &s,
		vector<vector<Var> > &o,
		vector<vector<Var> > &t,
		const int n, bool result )
{
	cout << (result? "SAT" : "UNSAT") << endl;
	if (result) {

		solver.printStats();

		cout << endl << endl;

		cout << "           " << "\t";
		for(int i=0; i<n; i++) cout << X << O;
		cout << endl;

		int place = 2*n;
		for( int i=0; i<n-1; i++ ) {
			for( int j=0; j<Len-1; j++ ) {
				if ( solver.getValue( t[i][j] ) ) {
					cout <<  std::setw(3) << j;
					cout << " --> " << std::setw(3)  << place << '\t';
					place = j;
					break;
				}
			}
			for( int j=0; j<Len; j++ ) {
				if ( !solver.getValue( s[i+1][j] ) ) {
					cout << (solver.getValue(o[i+1][j]) ? O : X );
				} else cout << " ";
			}
			cout << endl;
		}

		cout << "  0 --> " << std::setw(3)  << 2*n-1 << "\t  ";
		for(int i=0; i<n; i++) cout << O;
		for(int i=0; i<n; i++) cout << X;
	}
}

int main(int argc, char** argv)
{
	SatSolver solver;
	solver.initialize();

	vector<vector<Var> > s, o, x, t;

	assert(argc==2);

	int n = atoi(argv[1]);
	assert(n>=4);

	// TODO: modify translayer and remove the buffer
	Buff = 2;
	Len = 2*n+Buff;
 
	solver.assumeRelease();  // Clear assumptions
	genProofModel(solver, s, o, x, t, n);


	bool result;
	solver.printStats();

	time_t t_begin = clock();
	result = solver.solve();
	cout << "solved in " << clock() - t_begin  << " ticks."<< endl;
	solver.printStats();

	reportResult(solver, s, o, t, n, result );
	cout << endl << endl << "======================" << endl;
}
