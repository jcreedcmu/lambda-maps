var data = [
  {
    "term": {
      "tree": {
        "type": "bin",
        "subtype": "slam",
        "L": {
          "type": "var"
        },
        "R": {
          "type": "bin",
          "subtype": "lam",
          "L": {
            "type": "var"
          },
          "R": {
            "type": "bin",
            "subtype": "app",
            "L": {
              "type": "var"
            },
            "R": {
              "type": "bin",
              "subtype": "slam",
              "L": {
                "type": "var"
              },
              "R": {
                "type": "bin",
                "subtype": "app",
                "L": {
                  "type": "var"
                },
                "R": {
                  "type": "bin",
                  "subtype": "slam",
                  "L": {
                    "type": "var"
                  },
                  "R": {
                    "type": "bin",
                    "subtype": "app",
                    "L": {
                      "type": "var"
                    },
                    "R": {
                      "type": "var"
                    }
                  }
                }
              }
            }
          }
        }
      },
      "conn": [
        [
          0,
          4
        ],
        [
          1,
          2
        ],
        [
          3,
          7
        ],
        [
          5,
          6
        ]
      ],
      "front": [
        [
          "left",
          "slam"
        ],
        [
          "left",
          "lam"
        ],
        [
          "left",
          "app"
        ],
        [
          "left",
          "slam"
        ],
        [
          "left",
          "app"
        ],
        [
          "left",
          "slam"
        ],
        [
          "left",
          "app"
        ],
        [
          "right",
          "app"
        ]
      ]
    },
    "type": {
      "tree": {
        "type": "bin",
        "subtype": "pos",
        "L": {
          "type": "bin",
          "subtype": "neg",
          "L": {
            "type": "bin",
            "subtype": "pos",
            "L": {
              "type": "bin",
              "subtype": "neg",
              "L": {
                "type": "var"
              },
              "R": {
                "type": "var"
              }
            },
            "R": {
              "type": "var"
            }
          },
          "R": {
            "type": "var"
          }
        },
        "R": {
          "type": "bin",
          "subtype": "pos",
          "L": {
            "type": "bin",
            "subtype": "neg",
            "L": {
              "type": "bin",
              "subtype": "pos",
              "L": {
                "type": "var"
              },
              "R": {
                "type": "var"
              }
            },
            "R": {
              "type": "var"
            }
          },
          "R": {
            "type": "var"
          }
        }
      },
      "conn": [
        [
          0,
          4
        ],
        [
          1,
          2
        ],
        [
          3,
          5
        ],
        [
          6,
          7
        ]
      ],
      "front": [
        [
          "left",
          "neg"
        ],
        [
          "right",
          "neg"
        ],
        [
          "right",
          "pos"
        ],
        [
          "right",
          "neg"
        ],
        [
          "left",
          "pos"
        ],
        [
          "right",
          "pos"
        ],
        [
          "right",
          "neg"
        ],
        [
          "right",
          "pos"
        ]
      ]
    },
    "trin": {
      "tree": {
        "type": "bin",
        "subtype": "lamv",
        "L": {
          "type": "bin",
          "subtype": "fuse",
          "L": {
            "type": "bin",
            "subtype": "lamv",
            "L": {
              "type": "bin",
              "subtype": "fuse",
              "L": {
                "type": "var"
              },
              "R": {
                "type": "un",
                "subtype": "marker",
                "B": {
                  "type": "var"
                }
              }
            },
            "R": {
              "type": "var"
            }
          },
          "R": {
            "type": "un",
            "subtype": "marker",
            "B": {
              "type": "bin",
              "subtype": "fuse",
              "L": {
                "type": "bin",
                "subtype": "lamv",
                "L": {
                  "type": "bin",
                  "subtype": "lame",
                  "L": {
                    "type": "var"
                  },
                  "R": {
                    "type": "var"
                  }
                },
                "R": {
                  "type": "var"
                }
              },
              "R": {
                "type": "un",
                "subtype": "marker",
                "B": {
                  "type": "var"
                }
              }
            }
          }
        },
        "R": {
          "type": "var"
        }
      },
      "conn": [
        [
          0,
          3
        ],
        [
          1,
          2
        ],
        [
          4,
          5
        ],
        [
          6,
          7
        ]
      ],
      "front": [
        [
          "left",
          "fuse"
        ],
        [
          "left",
          "marker"
        ],
        [
          "right",
          "lamv"
        ],
        [
          "left",
          "lame"
        ],
        [
          "right",
          "lame"
        ],
        [
          "right",
          "lamv"
        ],
        [
          "left",
          "marker"
        ],
        [
          "right",
          "lamv"
        ]
      ]
    },
    "term_string": "/x./y.y (/z.x (/u.u z))",
    "type_string": "(((A >-> B) ->> B) >-> C) ->> ((A ->> C) >-> D) ->> D",
    "trinity_string": "((((t0 * ( M t1)) E t1) * ( M (((t0 V t2) E t2) * ( M t3)))) E t3)",
    "locally_orientable": false,
    "orientable": false
  },
  {
    "term": {
      "tree": {
        "type": "bin",
        "subtype": "slam",
        "L": {
          "type": "var"
        },
        "R": {
          "type": "bin",
          "subtype": "lam",
          "L": {
            "type": "var"
          },
          "R": {
            "type": "bin",
            "subtype": "app",
            "L": {
              "type": "var"
            },
            "R": {
              "type": "bin",
              "subtype": "slam",
              "L": {
                "type": "var"
              },
              "R": {
                "type": "bin",
                "subtype": "app",
                "L": {
                  "type": "var"
                },
                "R": {
                  "type": "bin",
                  "subtype": "slam",
                  "L": {
                    "type": "var"
                  },
                  "R": {
                    "type": "bin",
                    "subtype": "app",
                    "L": {
                      "type": "var"
                    },
                    "R": {
                      "type": "var"
                    }
                  }
                }
              }
            }
          }
        }
      },
      "conn": [
        [
          0,
          4
        ],
        [
          1,
          2
        ],
        [
          3,
          6
        ],
        [
          5,
          7
        ]
      ],
      "front": [
        [
          "left",
          "slam"
        ],
        [
          "left",
          "lam"
        ],
        [
          "left",
          "app"
        ],
        [
          "left",
          "slam"
        ],
        [
          "left",
          "app"
        ],
        [
          "left",
          "slam"
        ],
        [
          "left",
          "app"
        ],
        [
          "right",
          "app"
        ]
      ]
    },
    "type": {
      "tree": {
        "type": "bin",
        "subtype": "pos",
        "L": {
          "type": "bin",
          "subtype": "neg",
          "L": {
            "type": "bin",
            "subtype": "pos",
            "L": {
              "type": "var"
            },
            "R": {
              "type": "var"
            }
          },
          "R": {
            "type": "var"
          }
        },
        "R": {
          "type": "bin",
          "subtype": "pos",
          "L": {
            "type": "bin",
            "subtype": "neg",
            "L": {
              "type": "bin",
              "subtype": "pos",
              "L": {
                "type": "bin",
                "subtype": "neg",
                "L": {
                  "type": "var"
                },
                "R": {
                  "type": "var"
                }
              },
              "R": {
                "type": "var"
              }
            },
            "R": {
              "type": "var"
            }
          },
          "R": {
            "type": "var"
          }
        }
      },
      "conn": [
        [
          0,
          3
        ],
        [
          1,
          4
        ],
        [
          2,
          5
        ],
        [
          6,
          7
        ]
      ],
      "front": [
        [
          "left",
          "pos"
        ],
        [
          "right",
          "pos"
        ],
        [
          "right",
          "neg"
        ],
        [
          "left",
          "neg"
        ],
        [
          "right",
          "neg"
        ],
        [
          "right",
          "pos"
        ],
        [
          "right",
          "neg"
        ],
        [
          "right",
          "pos"
        ]
      ]
    },
    "trin": {
      "tree": {
        "type": "bin",
        "subtype": "lamv",
        "L": {
          "type": "bin",
          "subtype": "fuse",
          "L": {
            "type": "bin",
            "subtype": "lamv",
            "L": {
              "type": "bin",
              "subtype": "lame",
              "L": {
                "type": "var"
              },
              "R": {
                "type": "var"
              }
            },
            "R": {
              "type": "var"
            }
          },
          "R": {
            "type": "un",
            "subtype": "marker",
            "B": {
              "type": "bin",
              "subtype": "fuse",
              "L": {
                "type": "bin",
                "subtype": "lamv",
                "L": {
                  "type": "bin",
                  "subtype": "fuse",
                  "L": {
                    "type": "var"
                  },
                  "R": {
                    "type": "un",
                    "subtype": "marker",
                    "B": {
                      "type": "var"
                    }
                  }
                },
                "R": {
                  "type": "var"
                }
              },
              "R": {
                "type": "un",
                "subtype": "marker",
                "B": {
                  "type": "var"
                }
              }
            }
          }
        },
        "R": {
          "type": "var"
        }
      },
      "conn": [
        [
          0,
          3
        ],
        [
          1,
          2
        ],
        [
          4,
          5
        ],
        [
          6,
          7
        ]
      ],
      "front": [
        [
          "left",
          "lame"
        ],
        [
          "right",
          "lame"
        ],
        [
          "right",
          "lamv"
        ],
        [
          "left",
          "fuse"
        ],
        [
          "left",
          "marker"
        ],
        [
          "right",
          "lamv"
        ],
        [
          "left",
          "marker"
        ],
        [
          "right",
          "lamv"
        ]
      ]
    },
    "term_string": "/x./y.y (/z.x (/u.z u))",
    "type_string": "((A ->> B) >-> C) ->> (((A >-> B) ->> C) >-> D) ->> D",
    "trinity_string": "((((t0 V t1) E t1) * ( M (((t0 * ( M t2)) E t2) * ( M t3)))) E t3)",
    "locally_orientable": false,
    "orientable": false
  },
  {
    "term": {
      "tree": {
        "type": "bin",
        "subtype": "slam",
        "L": {
          "type": "var"
        },
        "R": {
          "type": "bin",
          "subtype": "lam",
          "L": {
            "type": "var"
          },
          "R": {
            "type": "bin",
            "subtype": "app",
            "L": {
              "type": "var"
            },
            "R": {
              "type": "bin",
              "subtype": "slam",
              "L": {
                "type": "var"
              },
              "R": {
                "type": "bin",
                "subtype": "app",
                "L": {
                  "type": "var"
                },
                "R": {
                  "type": "bin",
                  "subtype": "slam",
                  "L": {
                    "type": "var"
                  },
                  "R": {
                    "type": "bin",
                    "subtype": "app",
                    "L": {
                      "type": "var"
                    },
                    "R": {
                      "type": "var"
                    }
                  }
                }
              }
            }
          }
        }
      },
      "conn": [
        [
          0,
          2
        ],
        [
          1,
          4
        ],
        [
          3,
          7
        ],
        [
          5,
          6
        ]
      ],
      "front": [
        [
          "left",
          "slam"
        ],
        [
          "left",
          "lam"
        ],
        [
          "left",
          "app"
        ],
        [
          "left",
          "slam"
        ],
        [
          "left",
          "app"
        ],
        [
          "left",
          "slam"
        ],
        [
          "left",
          "app"
        ],
        [
          "right",
          "app"
        ]
      ]
    },
    "type": {
      "tree": {
        "type": "bin",
        "subtype": "pos",
        "L": {
          "type": "bin",
          "subtype": "neg",
          "L": {
            "type": "bin",
            "subtype": "pos",
            "L": {
              "type": "var"
            },
            "R": {
              "type": "var"
            }
          },
          "R": {
            "type": "var"
          }
        },
        "R": {
          "type": "bin",
          "subtype": "pos",
          "L": {
            "type": "bin",
            "subtype": "neg",
            "L": {
              "type": "bin",
              "subtype": "pos",
              "L": {
                "type": "bin",
                "subtype": "neg",
                "L": {
                  "type": "var"
                },
                "R": {
                  "type": "var"
                }
              },
              "R": {
                "type": "var"
              }
            },
            "R": {
              "type": "var"
            }
          },
          "R": {
            "type": "var"
          }
        }
      },
      "conn": [
        [
          0,
          3
        ],
        [
          1,
          6
        ],
        [
          2,
          7
        ],
        [
          4,
          5
        ]
      ],
      "front": [
        [
          "left",
          "pos"
        ],
        [
          "right",
          "pos"
        ],
        [
          "right",
          "neg"
        ],
        [
          "left",
          "neg"
        ],
        [
          "right",
          "neg"
        ],
        [
          "right",
          "pos"
        ],
        [
          "right",
          "neg"
        ],
        [
          "right",
          "pos"
        ]
      ]
    },
    "trin": {
      "tree": {
        "type": "bin",
        "subtype": "lamv",
        "L": {
          "type": "bin",
          "subtype": "fuse",
          "L": {
            "type": "bin",
            "subtype": "lamv",
            "L": {
              "type": "bin",
              "subtype": "lame",
              "L": {
                "type": "var"
              },
              "R": {
                "type": "var"
              }
            },
            "R": {
              "type": "var"
            }
          },
          "R": {
            "type": "un",
            "subtype": "marker",
            "B": {
              "type": "bin",
              "subtype": "fuse",
              "L": {
                "type": "bin",
                "subtype": "lamv",
                "L": {
                  "type": "bin",
                  "subtype": "fuse",
                  "L": {
                    "type": "var"
                  },
                  "R": {
                    "type": "un",
                    "subtype": "marker",
                    "B": {
                      "type": "var"
                    }
                  }
                },
                "R": {
                  "type": "var"
                }
              },
              "R": {
                "type": "un",
                "subtype": "marker",
                "B": {
                  "type": "var"
                }
              }
            }
          }
        },
        "R": {
          "type": "var"
        }
      },
      "conn": [
        [
          0,
          3
        ],
        [
          1,
          2
        ],
        [
          4,
          5
        ],
        [
          6,
          7
        ]
      ],
      "front": [
        [
          "left",
          "lame"
        ],
        [
          "right",
          "lame"
        ],
        [
          "right",
          "lamv"
        ],
        [
          "left",
          "fuse"
        ],
        [
          "left",
          "marker"
        ],
        [
          "right",
          "lamv"
        ],
        [
          "left",
          "marker"
        ],
        [
          "right",
          "lamv"
        ]
      ]
    },
    "term_string": "/x./y.x (/z.y (/u.u z))",
    "type_string": "((A ->> B) >-> C) ->> (((A >-> D) ->> D) >-> B) ->> C",
    "trinity_string": "((((t0 V t1) E t1) * ( M (((t0 * ( M t2)) E t2) * ( M t3)))) E t3)",
    "locally_orientable": false,
    "orientable": false
  },
  {
    "term": {
      "tree": {
        "type": "bin",
        "subtype": "slam",
        "L": {
          "type": "var"
        },
        "R": {
          "type": "bin",
          "subtype": "lam",
          "L": {
            "type": "var"
          },
          "R": {
            "type": "bin",
            "subtype": "app",
            "L": {
              "type": "var"
            },
            "R": {
              "type": "bin",
              "subtype": "slam",
              "L": {
                "type": "var"
              },
              "R": {
                "type": "bin",
                "subtype": "app",
                "L": {
                  "type": "var"
                },
                "R": {
                  "type": "bin",
                  "subtype": "slam",
                  "L": {
                    "type": "var"
                  },
                  "R": {
                    "type": "bin",
                    "subtype": "app",
                    "L": {
                      "type": "var"
                    },
                    "R": {
                      "type": "var"
                    }
                  }
                }
              }
            }
          }
        }
      },
      "conn": [
        [
          0,
          2
        ],
        [
          1,
          4
        ],
        [
          3,
          6
        ],
        [
          5,
          7
        ]
      ],
      "front": [
        [
          "left",
          "slam"
        ],
        [
          "left",
          "lam"
        ],
        [
          "left",
          "app"
        ],
        [
          "left",
          "slam"
        ],
        [
          "left",
          "app"
        ],
        [
          "left",
          "slam"
        ],
        [
          "left",
          "app"
        ],
        [
          "right",
          "app"
        ]
      ]
    },
    "type": {
      "tree": {
        "type": "bin",
        "subtype": "pos",
        "L": {
          "type": "bin",
          "subtype": "neg",
          "L": {
            "type": "bin",
            "subtype": "pos",
            "L": {
              "type": "bin",
              "subtype": "neg",
              "L": {
                "type": "var"
              },
              "R": {
                "type": "var"
              }
            },
            "R": {
              "type": "var"
            }
          },
          "R": {
            "type": "var"
          }
        },
        "R": {
          "type": "bin",
          "subtype": "pos",
          "L": {
            "type": "bin",
            "subtype": "neg",
            "L": {
              "type": "bin",
              "subtype": "pos",
              "L": {
                "type": "var"
              },
              "R": {
                "type": "var"
              }
            },
            "R": {
              "type": "var"
            }
          },
          "R": {
            "type": "var"
          }
        }
      },
      "conn": [
        [
          0,
          4
        ],
        [
          1,
          5
        ],
        [
          2,
          6
        ],
        [
          3,
          7
        ]
      ],
      "front": [
        [
          "left",
          "neg"
        ],
        [
          "right",
          "neg"
        ],
        [
          "right",
          "pos"
        ],
        [
          "right",
          "neg"
        ],
        [
          "left",
          "pos"
        ],
        [
          "right",
          "pos"
        ],
        [
          "right",
          "neg"
        ],
        [
          "right",
          "pos"
        ]
      ]
    },
    "trin": {
      "tree": {
        "type": "bin",
        "subtype": "lamv",
        "L": {
          "type": "bin",
          "subtype": "fuse",
          "L": {
            "type": "bin",
            "subtype": "lamv",
            "L": {
              "type": "bin",
              "subtype": "fuse",
              "L": {
                "type": "var"
              },
              "R": {
                "type": "un",
                "subtype": "marker",
                "B": {
                  "type": "var"
                }
              }
            },
            "R": {
              "type": "var"
            }
          },
          "R": {
            "type": "un",
            "subtype": "marker",
            "B": {
              "type": "bin",
              "subtype": "fuse",
              "L": {
                "type": "bin",
                "subtype": "lamv",
                "L": {
                  "type": "bin",
                  "subtype": "lame",
                  "L": {
                    "type": "var"
                  },
                  "R": {
                    "type": "var"
                  }
                },
                "R": {
                  "type": "var"
                }
              },
              "R": {
                "type": "un",
                "subtype": "marker",
                "B": {
                  "type": "var"
                }
              }
            }
          }
        },
        "R": {
          "type": "var"
        }
      },
      "conn": [
        [
          0,
          3
        ],
        [
          1,
          2
        ],
        [
          4,
          5
        ],
        [
          6,
          7
        ]
      ],
      "front": [
        [
          "left",
          "fuse"
        ],
        [
          "left",
          "marker"
        ],
        [
          "right",
          "lamv"
        ],
        [
          "left",
          "lame"
        ],
        [
          "right",
          "lame"
        ],
        [
          "right",
          "lamv"
        ],
        [
          "left",
          "marker"
        ],
        [
          "right",
          "lamv"
        ]
      ]
    },
    "term_string": "/x./y.x (/z.y (/u.z u))",
    "type_string": "(((A >-> B) ->> C) >-> D) ->> ((A ->> B) >-> C) ->> D",
    "trinity_string": "((((t0 * ( M t1)) E t1) * ( M (((t0 V t2) E t2) * ( M t3)))) E t3)",
    "locally_orientable": false,
    "orientable": false
  }
]
