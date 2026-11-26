// GMP floating-point jet accelerator; numerical only. Mirrors #139's jet/first.
#include <gmpxx.h>
#include <sstream>
#include <iomanip>
#include <string>
struct Z {
  mpf_class x,y;
  Z(long a=0):x(a),y(0){}
  Z(const mpf_class& a,const mpf_class& b):x(a),y(b){}
  Z(const char* a,const char* b):x(a),y(b){}
};
Z operator+(const Z&a,const Z&b){return Z(a.x+b.x,a.y+b.y);}
Z operator*(const Z&a,const Z&b){return Z(a.x*b.x-a.y*b.y,a.x*b.y+a.y*b.x);}
Z twice(const Z&a){return Z(2*a.x,2*a.y);}
extern "C" const char* csjet(const char* cx,const char* cy,const char* zx,const char* zy,int p,int digits,int second){
 static thread_local std::string result;
 mpf_set_default_prec((digits+20)*4);
 Z c(cx,cy),z(zx,zy),a(1),b,h,d;
 for(int i=0;i<p;i++){
   if(second){h=twice(a*a+z*h);d=twice(a*b+z*d);}
   b=twice(z*b)+Z(1);a=twice(z*a);z=z*z+c;
   if(z.x*z.x+z.y*z.y>16){result="escape";return result.c_str();}
 }
 std::ostringstream os;os<<std::scientific<<std::setprecision(digits+8);
 for(const auto& w:{z,a,b,h,d})os<<w.x<<' '<<w.y<<' ';
 result=os.str();return result.c_str();
}
