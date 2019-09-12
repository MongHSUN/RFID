% aver = ground_truth('0701/30_1/', )
function aver = ground_truth(dir_name, file_name, from, to)
    
file = strcat(dir_name, file_name);
f = fopen(file, 'r');
res = textscan(f, "%s\n%s\n");
speed = str2num(char(res{2}));
%disp(res);
tmp = cell2mat(res{1});
[m, n] = size(tmp);
time = [];
for i = 1:m
  c = strsplit(tmp(i,:), {':'});
  value = strcat(c(1), c(2), c(3));
  time = [time; str2double(value(1))];
end
sum = 0;
count = 0;
for i = 1:m
    if time(i) >= from && time(i) <= to
        count = count + 1;
        sum = sum + speed(i);
    end
end
aver = sum / count;
fclose(f);
end