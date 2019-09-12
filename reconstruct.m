clc
clear
close all

file_dir = '0701/40_1/';
raw_name = '40_1.bin';
truth = '40_1.txt';

% preprocess
raw_path = strcat(file_dir, raw_name);
index_path = strcat(file_dir, 'index.txt');
f = fopen(index_path, 'r');
index = textscan(f, '%s %s');
tmp = cell2mat(index{2});
index = str2num(char(index{1}));
[m, n] = size(tmp);
time = [];
for i = 1:m
  c = strsplit(tmp(i,:), {':'});
  value = strcat(c(1), c(2), c(3));
  time = [time; str2double(value(1))];
end
% index = index - 2;
fclose(f);
f = fopen(raw_path, 'rb');
x_inter_1 = fread(f, 'float32');
raw = x_inter_1(1:2:end) + 1i*x_inter_1(2:2:end);
fclose(f);
dx = [];
dy = [];
dc = [];
f = fopen('1.txt', 'a+');
%f2 = fopen('3.txt', 'a+');
isPlot = true;
isLog = false;
minAngle = 1/4 * pi;
maxAngle = 1/10 * pi;
% a is the first EPC index, b is the last EPC index - 10
a = 30;
b = 30; 
for j = a:b
    start = j + 1;
    last  = j + 10;
    % set non-epc data to zero
    start_index = index(start);
    end_index = index(last) + 6849;
    round = index(start: last);
    round = round - start_index + 1;
    data2 = raw(start_index : end_index);
    % filter
    time_round = time(start:last);
    notrun = 0;
    for i = 1:last - start
        if time_round(i + 1) - time_round(i) > 0.02
            notrun = 2;
            break;
        end
    end
    if notrun > 1
        continue;
    end
    if isPlot
        figure();
        plot(abs(data2));
        xlabel('Number of samples');
        ylabel('Amplitude');
    end
     [m, n] = size(data2);
    for i = 2 : last - start + 1
        data2(round(i - 1) + 6850: round(i) - 1) = 0;
    end
    if isPlot
        figure();
        plot(abs(data2));
        xlabel('Number of samples');
        ylabel('Amplitude');
    end
    % interpolation
    x = [];
    y = [];
    for i = 1 : last - start + 1
        x = [x; round(i) + 65; round(i) + 3462; round(i) + 6849];
        y = [y; data2(round(i) + 65); data2(round(i) + 3462); data2(round(i) + 6849)];
    end
    xx = 1:m;
    yy = interp1(x,y,xx,'spline');
    if isPlot
        figure();
        plot(x,abs(y),'ob',xx,abs(yy),'-r');
        xlabel('Number of samples');
        ylabel('Amplitude');
    end
    for i = 2 : last - start + 1
        data2(round(i - 1) + 6850: round(i) - 1) = yy(round(i - 1) + 6850: round(i) - 1);
    end
    if isPlot
        figure();
        plot(abs(data2));
        xlabel('Number of samples');
        ylabel('Amplitude');
    end
    % fft
    x = [1:100]';
    shift = (x - 1) / (m * 10) * 2 * 10^6;
    fft_data = abs(fft(data2, m * 10));
    if isPlot
        figure();
        plot(x, abs(fft_data(1:100)));
        xlabel('Frequency shift (Hz)');
        ylabel('Amplitude');
        xlim([0 100]);
    end
    [tmp, tmp2] = findpeaks((fft_data(1:1000)), 'Threshold',1e-4);
    ii = 1; local = -1;
    for i = 1:10
       if tmp2(i) >= 4 && tmp(i) > local
            local = tmp(i);
            ii = i;
        end
    end
    if fft_data(1) / 10 > local || fft_data(2) / 10 > local || fft_data(3) / 10 > local
        continue;
    end
    freq = 925e6;
    lambda = physconst('LightSpeed')/freq;
    shift = (tmp2(ii) - 1) / (m * 10) * 2 * 10^6;
    estimate = dop2speed(shift / 2, lambda);
    if estimate < 1
        continue
    end
    % dx = [dx; estimate * 3.6];
    % disp(estimate * 3.6);
    ground = ground_truth(file_dir, truth, time(start), time(last));
    % disp(ground);
    dy = [dy; ground];
    inter = atan( tan(maxAngle) / (1 - (time(start) - time(1)) / (time(b+last-start+1) - time(1))*(1-tan(maxAngle)/tan(minAngle))));
    %inter = (time(start) - time(1)) / (time(b+last-start+1) - time(1)) * (1/4*pi - 1/10*pi) + 1/10*pi;
    dc = [dc; estimate * 3.6 / cos(inter)];
    if isLog
        fprintf(f, '%g\n', estimate * 3.6 / cos(inter) - ground);
        % fprintf(f2, '%g\n', estimate * 3.6 / cos(inter) - ground);
    end
    disp(j);
end
fclose(f);
%fclose(f2);
figure();
%plot(dx,'-or');
hold on;
plot(dy,'-ob');
[m,n] = size(dc);
plot(dc,'-xr');
axis([1 m 0 70]);
xlabel('Estimation round');
ylabel('Speed (km/hr)');
legend('Ground truth','Estimated speed');