static struct X{int x;} func(struct Y{void *y;} a) {
    return (struct X){0};
}

extern int printf(const char *, ...);

int main () {
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
        int i =0;
        break;
    }
return 0;
}
int **var[5];