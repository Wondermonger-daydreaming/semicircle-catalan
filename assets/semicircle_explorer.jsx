import { useState, useEffect, useRef, useCallback } from "react";

// Precomputed data (N=300, 25 samples per frame)
const DATA = {"bin_centers":[-2.9531,-2.8594,-2.7656,-2.6719,-2.5781,-2.4844,-2.3906,-2.2969,-2.2031,-2.1094,-2.0156,-1.9219,-1.8281,-1.7344,-1.6406,-1.5469,-1.4531,-1.3594,-1.2656,-1.1719,-1.0781,-0.9844,-0.8906,-0.7969,-0.7031,-0.6094,-0.5156,-0.4219,-0.3281,-0.2344,-0.1406,-0.0469,0.0469,0.1406,0.2344,0.3281,0.4219,0.5156,0.6094,0.7031,0.7969,0.8906,0.9844,1.0781,1.1719,1.2656,1.3594,1.4531,1.5469,1.6406,1.7344,1.8281,1.9219,2.0156,2.1094,2.2031,2.2969,2.3906,2.4844,2.5781,2.6719,2.7656,2.8594,2.9531],"bin_width":0.0938,"catalan_targets":[1,2,5,14,42],"N":300,"bandwidth":[{"param":1,"histogram":[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0.0028,0.2389,1.8688,3.2498,3.2299,1.8702,0.202,0.0043,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],"moments":[0.0099,0.0002,0,0,0]},{"param":2,"histogram":[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0.037,0.7993,1.9655,2.5458,2.4946,1.9868,0.7908,0.0469,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],"moments":[0.0167,0.0006,0,0,0]},{"param":3,"histogram":[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0.0028,0.2318,1.1548,1.8361,2.1291,2.149,1.8119,1.1506,0.1963,0.0043,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],"moments":[0.0233,0.0012,0.0001,0,0]},{"param":4,"histogram":[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0.0128,0.4452,1.317,1.6796,1.8503,1.8588,1.7166,1.2843,0.4892,0.0128,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],"moments":[0.0296,0.0018,0.0001,0,0]},{"param":5,"histogram":[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0.0014,0.0853,0.7424,1.2686,1.5659,1.6597,1.7308,1.5474,1.2473,0.7268,0.091,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],"moments":[0.0365,0.0028,0.0003,0,0]},{"param":6,"histogram":[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0.0057,0.2432,0.859,1.2601,1.4635,1.5332,1.5531,1.4165,1.2644,0.8533,0.2091,0.0057,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],"moments":[0.0434,0.0039,0.0005,0.0001,0]},{"param":7,"histogram":[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0.0199,0.3584,0.933,1.1947,1.3852,1.4549,1.4592,1.3497,1.1947,0.8974,0.4025,0.0171,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],"moments":[0.0494,0.0051,0.0007,0.0001,0]},{"param":8,"histogram":[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0.0754,0.5476,0.8974,1.1733,1.2871,1.3596,1.3383,1.3042,1.1406,0.9714,0.5134,0.0583,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],"moments":[0.0565,0.0066,0.001,0.0002,0]},{"param":9,"histogram":[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0.0014,0.1493,0.6101,0.9173,1.1236,1.2217,1.2985,1.2971,1.2516,1.1122,0.9344,0.6172,0.1308,0.0014,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],"moments":[0.0621,0.008,0.0013,0.0002,0.0001]},{"param":10,"histogram":[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0.0043,0.2361,0.694,0.9116,1.1108,1.1591,1.2075,1.2302,1.1918,1.0852,0.923,0.6556,0.2546,0.0028,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],"moments":[0.0691,0.0098,0.0018,0.0004,0.0001]},{"param":15,"histogram":[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0.0114,0.256,0.5504,0.7324,0.8562,0.9273,1.0012,1.0027,1.0041,1.0055,0.9401,0.8533,0.7211,0.5348,0.256,0.0142,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],"moments":[0.1006,0.0207,0.0054,0.0016,0.0005]},{"param":20,"histogram":[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0.0057,0.2048,0.4494,0.5831,0.6869,0.7808,0.8434,0.8747,0.8988,0.8832,0.8704,0.8249,0.7794,0.7111,0.5831,0.4665,0.2148,0.0057,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],"moments":[0.1315,0.0354,0.0121,0.0046,0.0019]},{"param":25,"histogram":[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0.0014,0.1636,0.3541,0.4779,0.6016,0.6528,0.7296,0.7694,0.7794,0.7979,0.8107,0.7694,0.7751,0.7282,0.6656,0.6158,0.4764,0.3442,0.1493,0.0043,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],"moments":[0.1619,0.0538,0.0227,0.0108,0.0056]},{"param":30,"histogram":[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0.0839,0.2873,0.411,0.5006,0.5774,0.6372,0.677,0.7012,0.7424,0.7268,0.741,0.7168,0.714,0.667,0.6514,0.5589,0.4964,0.3982,0.2887,0.0896,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],"moments":[0.1922,0.0757,0.0377,0.0213,0.0129]},{"param":40,"histogram":[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0.0128,0.1394,0.2873,0.3598,0.4196,0.502,0.5319,0.5717,0.5973,0.6229,0.6428,0.6528,0.65,0.6244,0.6229,0.613,0.5717,0.5319,0.4949,0.4338,0.3612,0.2731,0.1365,0.0128,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],"moments":[0.2525,0.131,0.0861,0.0641,0.0514]},{"param":50,"histogram":[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0.0185,0.1493,0.2375,0.3115,0.3897,0.421,0.4736,0.5148,0.5305,0.5504,0.5675,0.5845,0.5845,0.5831,0.5845,0.5717,0.5561,0.5305,0.4964,0.4821,0.4267,0.3684,0.3115,0.2546,0.1394,0.0284,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],"moments":[0.3077,0.1955,0.1579,0.1444,0.1425]},{"param":60,"histogram":[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0.0242,0.128,0.2233,0.2816,0.3271,0.3883,0.411,0.448,0.4779,0.4992,0.5077,0.5447,0.5262,0.5504,0.539,0.5333,0.539,0.5148,0.4949,0.4764,0.4466,0.4181,0.3755,0.3271,0.2916,0.2119,0.1351,0.0256,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],"moments":[0.362,0.2709,0.2576,0.2774,0.3224]},{"param":80,"histogram":[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0.0114,0.0896,0.1564,0.2204,0.2631,0.3044,0.3314,0.3655,0.3911,0.4224,0.4352,0.4494,0.4466,0.4907,0.4807,0.4764,0.4821,0.4636,0.4836,0.4679,0.4452,0.4409,0.4167,0.384,0.3712,0.33,0.3129,0.2517,0.2119,0.1636,0.091,0.0156,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],"moments":[0.4634,0.4463,0.5482,0.7636,1.1495]},{"param":100,"histogram":[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0.0014,0.037,0.1138,0.1735,0.1963,0.2389,0.2731,0.2916,0.3428,0.3428,0.3627,0.3925,0.4068,0.4224,0.4167,0.448,0.4352,0.4324,0.4423,0.4309,0.4452,0.4309,0.411,0.4068,0.3797,0.3669,0.3669,0.3228,0.3044,0.2688,0.2332,0.1991,0.1721,0.1124,0.0455,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],"moments":[0.5576,0.6491,0.9638,1.6213,2.9428]},{"param":120,"histogram":[0,0,0,0,0,0,0,0,0,0,0,0,0,0.0014,0.0526,0.1138,0.1621,0.1948,0.219,0.2532,0.2631,0.3015,0.3086,0.3484,0.3456,0.3698,0.3854,0.3812,0.4068,0.411,0.4068,0.4124,0.4082,0.4053,0.3954,0.4124,0.384,0.3883,0.3641,0.3541,0.3356,0.3157,0.3143,0.266,0.2517,0.2148,0.1963,0.155,0.1095,0.0512,0.0071,0,0,0,0,0,0,0,0,0,0,0,0,0],"moments":[0.6435,0.8637,1.4768,2.8571,5.9602]},{"param":150,"histogram":[0,0,0,0,0,0,0,0,0,0,0,0,0.0085,0.0711,0.1337,0.1593,0.1835,0.2148,0.2219,0.2503,0.2802,0.2873,0.2958,0.3243,0.3328,0.3371,0.3499,0.3655,0.374,0.3812,0.3854,0.3826,0.3826,0.3769,0.374,0.3755,0.3641,0.3499,0.3442,0.3314,0.3243,0.2987,0.293,0.2674,0.2446,0.2418,0.2076,0.1892,0.1621,0.1195,0.074,0.0071,0,0,0,0,0,0,0,0,0,0,0,0],"moments":[0.7537,1.1816,2.3476,5.2569,12.6552]},{"param":200,"histogram":[0,0,0,0,0,0,0,0,0,0,0,0.0185,0.091,0.1351,0.1593,0.1792,0.2148,0.2318,0.2276,0.2674,0.2716,0.2716,0.2972,0.3072,0.3072,0.3172,0.3356,0.3228,0.3541,0.3399,0.33,0.347,0.3513,0.3356,0.3399,0.3428,0.3399,0.3285,0.31,0.3115,0.3058,0.2958,0.2773,0.2773,0.2517,0.2404,0.2318,0.1934,0.1963,0.1678,0.118,0.0981,0.027,0,0,0,0,0,0,0,0,0,0,0],"moments":[0.891,1.6188,3.7013,9.5118,26.2499]},{"param":250,"histogram":[0,0,0,0,0,0,0,0,0,0,0.01,0.0754,0.1109,0.1607,0.1721,0.2048,0.2076,0.2375,0.2432,0.2631,0.2588,0.2816,0.2859,0.2987,0.2873,0.32,0.3029,0.3129,0.3143,0.3342,0.3257,0.3143,0.3271,0.3129,0.3456,0.3086,0.3214,0.3086,0.3044,0.2958,0.3015,0.293,0.283,0.2645,0.2588,0.2503,0.2318,0.2091,0.2005,0.182,0.1564,0.1109,0.0725,0.0057,0,0,0,0,0,0,0,0,0,0],"moments":[0.9739,1.9067,4.6771,12.8696,37.9898]},{"param":300,"histogram":[0,0,0,0,0,0,0,0,0,0,0.0185,0.0782,0.1337,0.1522,0.1835,0.2005,0.2133,0.2332,0.2517,0.2546,0.2745,0.2773,0.283,0.2944,0.3001,0.293,0.3214,0.3086,0.3143,0.3157,0.3157,0.3143,0.3214,0.3115,0.32,0.3186,0.3001,0.3129,0.3086,0.2972,0.2916,0.283,0.2859,0.2674,0.2546,0.2432,0.2389,0.2076,0.2005,0.182,0.1607,0.1209,0.0853,0.0213,0.0014,0,0,0,0,0,0,0,0,0],"moments":[0.9991,1.9992,5.0113,14.0942,42.5347]}],"sparsity":[{"param":0.005,"histogram":[0.0014,0.0028,0.0071,0.0128,0.0157,0.0285,0.037,0.0313,0.0427,0.0527,0.0769,0.0783,0.0925,0.1067,0.1281,0.1423,0.1324,0.138,0.1608,0.1722,0.1836,0.1807,0.2234,0.2263,0.2362,0.2419,0.2661,0.2718,0.2832,0.3046,0.3231,1.1357,1.12,0.3273,0.3031,0.2918,0.259,0.2647,0.2462,0.2405,0.2263,0.2291,0.1807,0.1722,0.1751,0.1708,0.1295,0.1437,0.1309,0.1281,0.1153,0.0868,0.084,0.0697,0.0569,0.0455,0.0313,0.0384,0.0228,0.0171,0.0142,0.0071,0.0014,0],"moments":[1.0016,3.0395,13.1671,72.1104,489.6329]},{"param":0.01,"histogram":[0,0,0,0.0014,0.0028,0.0071,0.0199,0.0228,0.0356,0.0412,0.0754,0.0967,0.0996,0.1223,0.1237,0.1636,0.165,0.1721,0.1963,0.2091,0.2204,0.2361,0.2418,0.2645,0.2788,0.2802,0.2816,0.3129,0.3257,0.3541,0.3996,0.5916,0.5959,0.3911,0.3499,0.3243,0.2916,0.2958,0.2887,0.2802,0.2603,0.246,0.2389,0.2133,0.2076,0.1934,0.1749,0.1692,0.1465,0.1408,0.1081,0.1138,0.0896,0.0654,0.0526,0.0284,0.0299,0.0171,0.0071,0.0014,0.0028,0,0,0],"moments":[0.9918,2.4614,8.2678,32.825,145.6112]},{"param":0.02,"histogram":[0,0,0,0,0,0,0.0014,0.0057,0.0213,0.0427,0.0725,0.0939,0.1166,0.1223,0.155,0.1678,0.1792,0.2162,0.2048,0.2418,0.2375,0.2475,0.2731,0.2773,0.2887,0.3044,0.3015,0.33,0.3371,0.3413,0.3669,0.3897,0.3854,0.3684,0.347,0.3371,0.32,0.3086,0.2987,0.2916,0.2716,0.2773,0.2489,0.246,0.2276,0.202,0.2062,0.1877,0.1692,0.1564,0.1337,0.1124,0.0882,0.0725,0.0427,0.0256,0.0043,0.0014,0,0,0,0,0,0],"moments":[1.003,2.2527,6.5991,22.2176,81.6671]},{"param":0.05,"histogram":[0,0,0,0,0,0,0,0,0.0014,0.0156,0.0583,0.0896,0.1223,0.1508,0.1678,0.1806,0.1963,0.2233,0.2304,0.2489,0.2588,0.2546,0.2802,0.293,0.293,0.3072,0.31,0.3157,0.3356,0.33,0.3385,0.3342,0.3428,0.3342,0.3285,0.3257,0.3143,0.3058,0.3186,0.2972,0.2844,0.2716,0.2802,0.2603,0.2347,0.2304,0.2148,0.2062,0.192,0.1678,0.1351,0.1252,0.0924,0.0555,0.0114,0.0014,0,0,0,0,0,0,0,0],"moments":[0.9981,2.0896,5.5731,16.8341,54.9077]},{"param":0.1,"histogram":[0,0,0,0,0,0,0,0,0,0.0014,0.0498,0.0754,0.1252,0.1536,0.1764,0.1934,0.2034,0.2375,0.2347,0.2404,0.2631,0.2788,0.2816,0.2873,0.3029,0.3072,0.3015,0.3228,0.3257,0.3214,0.3143,0.3428,0.3214,0.3228,0.3271,0.3172,0.3228,0.3157,0.2987,0.2958,0.2944,0.2788,0.2702,0.2773,0.246,0.2332,0.2233,0.2062,0.192,0.1707,0.1593,0.118,0.091,0.0441,0,0,0,0,0,0,0,0,0,0],"moments":[0.9961,2.0356,5.2552,15.2899,47.8732]},{"param":0.2,"histogram":[0,0,0,0,0,0,0,0,0,0,0.0299,0.0882,0.1252,0.1522,0.1778,0.1892,0.229,0.2247,0.2418,0.2631,0.2489,0.2873,0.2745,0.2916,0.293,0.3214,0.3058,0.3058,0.3157,0.3243,0.32,0.3214,0.3186,0.3257,0.32,0.3143,0.32,0.3044,0.3001,0.3015,0.283,0.2916,0.2702,0.2631,0.2631,0.2489,0.2233,0.2261,0.1877,0.1721,0.1621,0.1252,0.0924,0.0228,0,0,0,0,0,0,0,0,0,0],"moments":[0.9994,2.0176,5.1136,14.5562,44.4839]},{"param":0.3,"histogram":[0,0,0,0,0,0,0,0,0,0,0.0228,0.0882,0.128,0.1607,0.1707,0.2048,0.2076,0.2418,0.2389,0.2617,0.2603,0.283,0.2788,0.2859,0.3015,0.3086,0.3058,0.3115,0.3143,0.32,0.3157,0.3243,0.3143,0.3314,0.31,0.3214,0.32,0.3044,0.3115,0.2844,0.2916,0.2887,0.2759,0.2546,0.2688,0.2432,0.2361,0.2048,0.1977,0.1792,0.1564,0.1237,0.0825,0.0313,0,0,0,0,0,0,0,0,0,0],"moments":[0.9993,2.0149,5.0973,14.48,44.162]},{"param":0.5,"histogram":[0,0,0,0,0,0,0,0,0,0,0.0242,0.0839,0.1294,0.1493,0.1948,0.1835,0.229,0.219,0.2517,0.2517,0.2674,0.2773,0.2859,0.2987,0.2802,0.3115,0.3172,0.3157,0.3115,0.3157,0.32,0.3228,0.32,0.3129,0.3115,0.3143,0.3044,0.3186,0.3129,0.2944,0.2958,0.283,0.2702,0.2688,0.2603,0.2546,0.2233,0.219,0.1906,0.1835,0.165,0.1223,0.0796,0.0213,0,0,0,0,0,0,0,0,0,0],"moments":[0.9991,2.0069,5.0545,14.285,43.3167]},{"param":0.7,"histogram":[0,0,0,0,0,0,0,0,0,0,0.0156,0.0825,0.128,0.1522,0.1835,0.2034,0.219,0.2332,0.2489,0.2631,0.2603,0.2773,0.2816,0.2901,0.2972,0.3029,0.3143,0.32,0.3115,0.3172,0.3143,0.3129,0.3314,0.31,0.3157,0.3115,0.3157,0.3086,0.3029,0.2987,0.2873,0.2873,0.2702,0.2702,0.2532,0.256,0.2332,0.219,0.1991,0.182,0.1564,0.128,0.0896,0.01,0.0014,0,0,0,0,0,0,0,0,0],"moments":[0.9981,1.9939,4.9815,13.9514,41.9094]},{"param":1.0,"histogram":[0,0,0,0,0,0,0,0,0,0.0014,0.0156,0.0825,0.128,0.1536,0.1764,0.2048,0.2233,0.2375,0.2361,0.2574,0.2688,0.2859,0.2773,0.2987,0.293,0.3058,0.3044,0.3172,0.3172,0.3143,0.3143,0.3271,0.3115,0.3172,0.3115,0.3157,0.3157,0.3072,0.31,0.2859,0.2873,0.2972,0.2759,0.2702,0.2475,0.246,0.2375,0.2247,0.192,0.1849,0.165,0.1195,0.0839,0.0199,0,0,0,0,0,0,0,0,0,0],"moments":[0.9996,2.0008,5.0141,14.0979,42.5448]}]};

const semicircleDensity = (x) => {
  if (Math.abs(x) > 2) return 0;
  return Math.sqrt(4 - x * x) / (2 * Math.PI);
};

const MOMENT_LABELS = ["m₂", "m₄", "m₆", "m₈", "m₁₀"];
const CATALAN = DATA.catalan_targets;
const MOMENT_COLORS = ["#58a6ff", "#3fb950", "#f0883e", "#bc8cff", "#f778ba"];

function Histogram({ frame, maxY = 0.42 }) {
  const bins = DATA.bin_centers;
  const w = DATA.bin_width;
  const hist = frame.histogram;
  
  const svgW = 560, svgH = 280;
  const pad = { l: 45, r: 15, t: 10, b: 35 };
  const plotW = svgW - pad.l - pad.r;
  const plotH = svgH - pad.t - pad.b;
  
  const xScale = (v) => pad.l + ((v + 3) / 6) * plotW;
  const yScale = (v) => pad.t + plotH - (v / maxY) * plotH;
  
  // Semicircle curve
  const scPoints = [];
  for (let i = 0; i < 200; i++) {
    const x = -2 + (4 * i) / 199;
    const y = semicircleDensity(x);
    scPoints.push(`${xScale(x)},${yScale(y)}`);
  }
  
  return (
    <svg viewBox={`0 0 ${svgW} ${svgH}`} style={{ width: "100%", maxWidth: 560 }}>
      {/* Grid */}
      {[0, 0.1, 0.2, 0.3, 0.4].map(v => (
        <g key={v}>
          <line x1={pad.l} x2={svgW - pad.r} y1={yScale(v)} y2={yScale(v)} 
                stroke="#30363d" strokeWidth={0.5} />
          <text x={pad.l - 5} y={yScale(v) + 4} fill="#8b949e" fontSize={9} textAnchor="end">
            {v.toFixed(1)}
          </text>
        </g>
      ))}
      {/* X axis labels */}
      {[-2, -1, 0, 1, 2].map(v => (
        <text key={v} x={xScale(v)} y={svgH - 8} fill="#8b949e" fontSize={9} textAnchor="middle">
          {v}
        </text>
      ))}
      <text x={svgW / 2} y={svgH - 0} fill="#8b949e" fontSize={10} textAnchor="middle">eigenvalue</text>
      <text x={12} y={svgH / 2} fill="#8b949e" fontSize={10} textAnchor="middle"
            transform={`rotate(-90 12 ${svgH/2})`}>density</text>
      
      {/* Histogram bars */}
      {hist.map((h, i) => {
        const x = bins[i];
        const barH = Math.min(h, maxY);
        return (
          <rect key={i} x={xScale(x - w/2)} y={yScale(barH)} 
                width={Math.max(1, (w/6) * plotW - 0.5)} height={yScale(0) - yScale(barH)}
                fill="#58a6ff" opacity={0.7} rx={0.5} />
        );
      })}
      
      {/* Semicircle curve */}
      <polyline points={scPoints.join(" ")} fill="none" stroke="#f0883e" strokeWidth={2.5} />
    </svg>
  );
}

function MomentBars({ moments }) {
  const svgW = 280, svgH = 280;
  const pad = { l: 35, r: 10, t: 25, b: 45 };
  const plotW = svgW - pad.l - pad.r;
  const plotH = svgH - pad.t - pad.b;
  
  // Log scale for display (moments can vary hugely)
  const displayMoments = moments.slice(0, 4);
  const displayTargets = CATALAN.slice(0, 4);
  const maxVal = Math.max(...displayTargets.map((t, i) => Math.max(t, displayMoments[i] || 0)), 16);
  
  const barW = plotW / 5;
  const yScale = (v) => pad.t + plotH - (Math.min(v, maxVal) / maxVal) * plotH;
  
  return (
    <svg viewBox={`0 0 ${svgW} ${svgH}`} style={{ width: "100%", maxWidth: 280 }}>
      <text x={svgW / 2} y={14} fill="#e6edf3" fontSize={11} textAnchor="middle" fontWeight="600">
        moments vs Catalan targets
      </text>
      
      {/* Grid */}
      {[0, 5, 10, 14].map(v => (
        <g key={v}>
          <line x1={pad.l} x2={svgW - pad.r} y1={yScale(v)} y2={yScale(v)}
                stroke="#30363d" strokeWidth={0.5} />
          <text x={pad.l - 4} y={yScale(v) + 3} fill="#8b949e" fontSize={8} textAnchor="end">
            {v}
          </text>
        </g>
      ))}
      
      {displayTargets.map((target, i) => {
        const cx = pad.l + (i + 0.5) * barW + barW * 0.25;
        const val = displayMoments[i] || 0;
        const targetY = yScale(target);
        
        return (
          <g key={i}>
            {/* Target line */}
            <line x1={cx - barW * 0.35} x2={cx + barW * 0.35} y1={targetY} y2={targetY}
                  stroke={MOMENT_COLORS[i]} strokeWidth={2} strokeDasharray="4 2" opacity={0.5} />
            {/* Actual bar */}
            <rect x={cx - barW * 0.25} y={yScale(val)} 
                  width={barW * 0.5} height={Math.max(0, yScale(0) - yScale(val))}
                  fill={MOMENT_COLORS[i]} opacity={0.85} rx={2} />
            {/* Value label */}
            <text x={cx} y={yScale(val) - 4} fill={MOMENT_COLORS[i]} fontSize={8} 
                  textAnchor="middle" fontWeight="600">
              {val < 0.01 ? val.toFixed(4) : val < 1 ? val.toFixed(2) : val.toFixed(1)}
            </text>
            {/* Label */}
            <text x={cx} y={svgH - 25} fill="#c9d1d9" fontSize={9} textAnchor="middle">
              {MOMENT_LABELS[i]}
            </text>
            <text x={cx} y={svgH - 13} fill="#8b949e" fontSize={8} textAnchor="middle">
              →{target}
            </text>
          </g>
        );
      })}
    </svg>
  );
}

export default function SemicircleExplorer() {
  const [mode, setMode] = useState("bandwidth");
  const [frameIdx, setFrameIdx] = useState(0);
  const [playing, setPlaying] = useState(false);
  const intervalRef = useRef(null);
  
  const frames = mode === "bandwidth" ? DATA.bandwidth : DATA.sparsity;
  const frame = frames[Math.min(frameIdx, frames.length - 1)];
  
  useEffect(() => {
    setFrameIdx(0);
    setPlaying(false);
  }, [mode]);
  
  useEffect(() => {
    if (playing) {
      intervalRef.current = setInterval(() => {
        setFrameIdx(prev => {
          if (prev >= frames.length - 1) {
            setPlaying(false);
            return prev;
          }
          return prev + 1;
        });
      }, 250);
    }
    return () => clearInterval(intervalRef.current);
  }, [playing, frames.length]);
  
  const togglePlay = useCallback(() => {
    if (frameIdx >= frames.length - 1) {
      setFrameIdx(0);
      setPlaying(true);
    } else {
      setPlaying(p => !p);
    }
  }, [frameIdx, frames.length]);
  
  const paramLabel = mode === "bandwidth" 
    ? `bandwidth = ${frame.param} / ${DATA.N}`
    : `p = ${frame.param.toFixed(3)}`;
  
  const paramDetail = mode === "bandwidth"
    ? `${((frame.param / DATA.N) * 100).toFixed(1)}% of matrix width`
    : `${(frame.param * 100).toFixed(1)}% entries nonzero`;
  
  // Convergence score
  const m2err = Math.abs(frame.moments[0] - 1);
  const m4err = Math.abs(frame.moments[1] - 2);
  const convergence = Math.max(0, 100 - (m2err + m4err / 2) * 100);
  
  return (
    <div style={{
      background: "#0d1117",
      color: "#e6edf3",
      fontFamily: "'JetBrains Mono', 'Fira Code', 'SF Mono', monospace",
      padding: "20px",
      minHeight: "100vh",
      boxSizing: "border-box",
    }}>
      <div style={{ maxWidth: 880, margin: "0 auto" }}>
        {/* Title */}
        <h1 style={{ 
          fontSize: 18, fontWeight: 700, margin: "0 0 4px 0",
          background: "linear-gradient(90deg, #58a6ff, #f0883e)",
          WebkitBackgroundClip: "text", WebkitTextFillColor: "transparent",
        }}>
          Wigner Semicircle Explorer
        </h1>
        <p style={{ color: "#8b949e", fontSize: 12, margin: "0 0 16px 0" }}>
          Watch the semicircle law emerge as matrix structure changes. N = {DATA.N}, averaged over 25 samples.
        </p>
        
        {/* Mode tabs */}
        <div style={{ display: "flex", gap: 8, marginBottom: 16 }}>
          {[
            { key: "bandwidth", label: "Bandwidth", icon: "◐", desc: "band → full matrix" },
            { key: "sparsity", label: "Sparsity", icon: "◉", desc: "sparse → dense" },
          ].map(({ key, label, icon, desc }) => (
            <button key={key} onClick={() => setMode(key)} style={{
              flex: 1,
              padding: "10px 16px",
              background: mode === key ? "#161b22" : "transparent",
              border: `1px solid ${mode === key ? "#58a6ff" : "#30363d"}`,
              borderRadius: 8,
              color: mode === key ? "#58a6ff" : "#8b949e",
              cursor: "pointer",
              textAlign: "left",
              transition: "all 0.2s",
            }}>
              <div style={{ fontSize: 14, fontWeight: 600 }}>{icon} {label}</div>
              <div style={{ fontSize: 10, opacity: 0.7, marginTop: 2 }}>{desc}</div>
            </button>
          ))}
        </div>
        
        {/* Parameter display */}
        <div style={{
          background: "#161b22", border: "1px solid #30363d", borderRadius: 8,
          padding: "12px 16px", marginBottom: 12,
          display: "flex", justifyContent: "space-between", alignItems: "center",
        }}>
          <div>
            <div style={{ fontSize: 20, fontWeight: 700, color: mode === "bandwidth" ? "#58a6ff" : "#bc8cff" }}>
              {paramLabel}
            </div>
            <div style={{ fontSize: 11, color: "#8b949e" }}>{paramDetail}</div>
          </div>
          <div style={{ textAlign: "right" }}>
            <div style={{ fontSize: 11, color: "#8b949e" }}>semicircle fit</div>
            <div style={{ 
              fontSize: 20, fontWeight: 700,
              color: convergence > 90 ? "#3fb950" : convergence > 50 ? "#f0883e" : "#f85149",
            }}>
              {convergence.toFixed(0)}%
            </div>
          </div>
        </div>
        
        {/* Controls */}
        <div style={{ display: "flex", gap: 8, alignItems: "center", marginBottom: 12 }}>
          <button onClick={togglePlay} style={{
            width: 36, height: 36, borderRadius: "50%",
            background: "#161b22", border: "1px solid #30363d",
            color: "#58a6ff", cursor: "pointer", fontSize: 16,
            display: "flex", alignItems: "center", justifyContent: "center",
          }}>
            {playing ? "⏸" : (frameIdx >= frames.length - 1 ? "↺" : "▶")}
          </button>
          <input type="range" min={0} max={frames.length - 1} value={frameIdx}
            onChange={(e) => { setFrameIdx(+e.target.value); setPlaying(false); }}
            style={{ flex: 1, accentColor: mode === "bandwidth" ? "#58a6ff" : "#bc8cff" }}
          />
          <span style={{ fontSize: 10, color: "#8b949e", minWidth: 60, textAlign: "right" }}>
            {frameIdx + 1} / {frames.length}
          </span>
        </div>
        
        {/* Visualization panels */}
        <div style={{ display: "flex", gap: 12, flexWrap: "wrap" }}>
          <div style={{
            flex: "1 1 520px",
            background: "#161b22", border: "1px solid #30363d", borderRadius: 8,
            padding: "12px",
          }}>
            <Histogram frame={frame} />
          </div>
          <div style={{
            flex: "0 1 280px",
            background: "#161b22", border: "1px solid #30363d", borderRadius: 8,
            padding: "12px",
          }}>
            <MomentBars moments={frame.moments} />
          </div>
        </div>
        
        {/* Insight text */}
        <div style={{
          marginTop: 12, padding: "10px 14px",
          background: "#161b22", border: "1px solid #30363d", borderRadius: 8,
          fontSize: 11, color: "#8b949e", lineHeight: 1.5,
        }}>
          {mode === "bandwidth" && frame.param <= 10 && (
            <span>At very small bandwidth, only a few diagonals contribute. The eigenvalue distribution is concentrated in a narrow spike — essentially a rescaled version of the single-entry distribution. The semicircle has not yet begun to form.</span>
          )}
          {mode === "bandwidth" && frame.param > 10 && frame.param <= 50 && (
            <span>The distribution is broadening as more diagonals participate, beginning to develop the characteristic flat-topped shape. But the support is still narrower than [−2, 2] and the moments fall well short of the Catalan targets. The band constraint breaks full universality.</span>
          )}
          {mode === "bandwidth" && frame.param > 50 && frame.param <= 150 && (
            <span>Now the transition is visible — the histogram is acquiring the semicircular profile and the support is approaching [−2, 2]. The moments are climbing toward their Catalan values. The matrix is "full enough" for the law of large numbers across eigenvalues to start asserting itself.</span>
          )}
          {mode === "bandwidth" && frame.param > 150 && (
            <span>The full Wigner matrix. The semicircle law is clearly visible, and the empirical moments are landing on the Catalan numbers: m₂ ≈ 1, m₄ ≈ 2, m₆ ≈ 5, m₈ ≈ 14. The non-crossing pairings have won.</span>
          )}
          {mode === "sparsity" && frame.param <= 0.02 && (
            <span>Extremely sparse — most entries are zero. The distribution shows a prominent spike at the origin (isolated eigenvalues from near-empty rows) plus broad tails. The higher moments explode far above the Catalan targets. This is a qualitatively different spectral regime.</span>
          )}
          {mode === "sparsity" && frame.param > 0.02 && frame.param <= 0.1 && (
            <span>As density increases, the central spike dissolves and the semicircular shape begins to emerge. The key: we rescale entries by 1/√p to maintain variance, so the semicircle should reappear if the matrix is "connected enough." The moments are drifting toward their targets but higher moments still overshoot.</span>
          )}
          {mode === "sparsity" && frame.param > 0.1 && frame.param < 0.5 && (
            <span>The semicircle is clearly forming. The rescaling has done its work — even with most entries missing, the eigenvalue distribution is converging to the universal shape. The transition threshold for sparse Wigner matrices is around p ~ log(N)/N; we're well above that here.</span>
          )}
          {mode === "sparsity" && frame.param >= 0.5 && (
            <span>Dense enough to be indistinguishable from the full Wigner case. All moments are essentially at their Catalan targets. The semicircle is robust — it doesn't need every entry, just enough to establish the collective behavior that averaging demands.</span>
          )}
        </div>
        
        <div style={{
          marginTop: 10, fontSize: 10, color: "#484f58", textAlign: "center",
        }}>
          drag the slider or press play to watch the transition · orange curve = semicircle law ρ(x) = √(4−x²) / 2π
        </div>
      </div>
    </div>
  );
}
