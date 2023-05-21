static struct X func(struct {void *y;} a) {
    return (struct X){0};
}
struct X;
struct X{int x;};

extern int printf(const char **, ...);

extern int a(int(**[0])());

int main () {
    func();
    goto label;
    struct Y a; 
    struct Y{int a;};
label :
    for (int i=0;i<5;i++){
        printf("%d",i);
        if (i==4)
        break;
        if (i<5)continue;
    }
    switch (0){
        case 0:
        case 1:
        default:
        int printf =0;
        break;
    }
return 0;
}
int **var[5] = "abc";